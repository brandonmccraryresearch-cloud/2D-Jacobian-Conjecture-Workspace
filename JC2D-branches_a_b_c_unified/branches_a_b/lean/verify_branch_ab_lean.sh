#!/usr/bin/env bash
# verify_branch_ab_lean.sh — verification script for the branch-(a,b) Lean 4 formalization.
# Runs the full build (unpiped, genuine exit status), checks the build log for `sorry`
# warnings, scans all sources for sorry/admit/user axioms outside comments, and prints the
# axiom dependencies of every theorem (must be exactly propext, Classical.choice, Quot.sound).
#
# Resources: the exact K5 descent (Jacobian/Descent, 84 modules) needs ~12 min on 4 cores and
# ~2 GB RAM per build job (peak ~7.5 GB total with 4 jobs); outputs ~2.5 GB of .olean files.
# The Prop. 6.1 proof (Jacobian/ChartProof, 12 modules, v17) needs ~25 min sequentially and up to
# 5.4 GB RAM for a single module (Stage2_g7); build with LEAN_NUM_THREADS=1 on machines with < 12 GB.
# The m = 3, 5 classifications (Jacobian/B26, 10 modules, added 2026-10-05) take ~8 min sequentially with
# LEAN_NUM_THREADS=1 and up to ~3.8 GB RAM for a single module (M5T; M5Rel1-3 ~2.4 GB);
# see scripts/b26_m5_eliminant/lean_certificates/.
#
# Usage: verify_branch_ab_lean.sh [PROJECT_DIR]
#   PROJECT_DIR defaults to this script's directory if it holds lakefile.toml,
#   otherwise to ~/workspace/jacobian_lean.
set -u
export PATH="$HOME/.elan/bin:$PATH"

HERE="$(cd "$(dirname "$0")" && pwd)"
if [ $# -ge 1 ]; then PROJ="$1"
elif [ -f "$HERE/lakefile.toml" ]; then PROJ="$HERE"
else PROJ=~/workspace/jacobian_lean
fi
LOG=/tmp/lean_verify.log
THEOREMS="t_zero_case minor_obstruction only_zero_transport
  t_zero_case_char t_zero_case_fails_char3 minor_vanish eval_minorPoly no_nonzero_direction
  isValuativelyProper2D_id isValuativelyProper2D_triangular isValuativelyProper2D_linear
  BranchAb.layer_bracket BranchAb.coeff_yev BranchAb.layers_eq_zero BranchAb.layers_of_jac
  BranchAb.coeff_layerTerm BranchAb.coeff_sc BranchAb.layerTerm_sc BranchAb.layers_transport
  BranchAb.Descent.descent_K5 BranchAb.layers_K5 BranchAb.no_completion_K5
  BranchAb.top_layer_E5 BranchAb.layers_K5_sharp
  BranchAb.latticeNP_card BranchAb.latticeNQ_card BranchAb.vertices_mem BranchAb.X1_pow_mul_layerPiece
  BranchAb.eq_sum_layerPiece BranchAb.coeff_layerPoly BranchAb.layers_of_support BranchAb.no_completion_K5_PQ
  BranchAb.belyi_derivative BranchAb.layerTerm_top BranchAb.orbit_solves_E5
  BranchAb.main_theorem_of_classification
  BranchAb.TopLayerSmall.m5_residual_iff BranchAb.TopLayerSmall.m5_chart_iff BranchAb.TopLayerSmall.m5_a4_ne_zero
  BranchAb.TopLayerSmall.m5_T_squarefree BranchAb.TopLayerSmall.m5_solution_formulas
  BranchAb.TopLayerSmall.m3_residual_iff BranchAb.TopLayerSmall.m3_chart_iff BranchAb.TopLayerSmall.m3_a2_ne_zero
  BranchAb.TopLayerSmall.m3_T_squarefree
  BranchAb.chart_K5_identities BranchAb.chart_point_solves BranchAb.topLayerClassification_of_chart
  BranchAb.main_theorem_of_chart
  BranchAb.ChartProof.eq_of_toPolyK BranchAb.ChartProof.lc_zero BranchAb.chartClassification_holds BranchAb.main_theorem"

cd "$PROJ" || { echo "FAIL: cannot cd to $PROJ"; exit 1; }
echo "project: $PROJ"

echo "=== 1. lake build (full project) ==="
lake build > "$LOG" 2>&1
status=$?
echo "lake build exit status: $status"
if [ "$status" -ne 0 ]; then
  echo "FAIL: build errors:"
  grep -E "error" "$LOG" | head -20
  exit 1
fi
# Lean 4.34 prints: declaration uses `sorry`  (older versions: 'sorry')
if grep -E "declaration uses .sorry." "$LOG"; then
  echo "FAIL: sorry warning in build log"
  exit 1
fi
echo "PASS: build clean"

echo "=== 2. sorry/admit/native_decide/user-axiom scan (all sources, comments stripped) ==="
python3 - Jacobian.lean $(find Jacobian -name '*.lean' | sort) <<'PY' || exit 1
import re, sys
bad = 0
for f in sys.argv[1:]:
    s = open(f).read()
    s = re.sub(r'/-.*?-/', '', s, flags=re.S)   # block and doc comments
    s = re.sub(r'--[^\n]*', '', s)              # line comments
    for l in s.splitlines():
        if re.search(r'\b(sorry|admit|native_decide)\b', l) or re.match(r'\s*(private\s+)?axiom\s', l):
            print(f"  {f}: {l.strip()}"); bad = 1
sys.exit(bad)
PY
if [ $? -ne 0 ]; then echo "FAIL: sorry/admit/axiom found above"; exit 1; fi
echo "PASS: no sorry, no admit, no native_decide, no user-declared axioms"

echo "=== 3. #print axioms ==="
{ echo "import Jacobian"; for t in $THEOREMS; do echo "#print axioms $t"; done; } > "$PROJ/AxiomCheck.lean"
lake env lean "$PROJ/AxiomCheck.lean" > /tmp/axiom_check.log 2>&1
axstatus=$?
rm -f "$PROJ/AxiomCheck.lean"
if [ "$axstatus" -ne 0 ]; then
  echo "FAIL: axiom check failed to elaborate"
  cat /tmp/axiom_check.log
  exit 1
fi
cat /tmp/axiom_check.log
if grep -q "sorryAx" /tmp/axiom_check.log; then
  echo "FAIL: sorryAx present in axiom dependencies"
  exit 1
fi
n_ok=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" /tmp/axiom_check.log)
n_all=$(echo $THEOREMS | wc -w)
if [ "$n_ok" -ne "$n_all" ]; then
  echo "FAIL: $n_ok of $n_all theorems have exactly the standard axioms"
  exit 1
fi
echo "PASS: all $n_all theorems depend only on propext, Classical.choice, Quot.sound"

echo "=== ALL CHECKS PASSED ==="
