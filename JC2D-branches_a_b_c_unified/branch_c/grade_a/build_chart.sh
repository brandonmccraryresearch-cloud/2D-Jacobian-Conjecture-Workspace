#!/usr/bin/env bash
# build_chart.sh -- the chart reduction of branch (c) and the interface theorem (Lean 4.34.0, Mathlib v4.34.0).
#
# Usage: build_chart.sh [BUNDLE_PROJECT]
#   BUNDLE_PROJECT is a Lake project in which the branch-(c) bundle is built, i.e. which has the compiled modules
#   Jacobian.BranchC.T1Zero.Combine, .Sq, .Defs and Jacobian.BranchC.CondsC (default ../bundle_v3_1/jacobian_lean,
#   after its own build). Nothing is written into it: the .olean files go to a temporary directory.
#
# Steps:
#   0. regenerate lean/GradeA/Chart/{Gens,F_*,Main}.lean with certgen/gen_chart_lean.py into a temporary directory
#      (which re-checks every certificate by exact integer arithmetic, and the generators against the rank check's
#      at p = 32003 and 1000003) and compare them byte for byte with the committed files;
#   1. scan lean/GradeA/*.lean and lean/GradeA/Chart/*.lean (comments stripped) for sorry, admit, native_decide and
#      user axioms;
#   2. compile R67Data, IrreducibleR, Transfer, Macaulay, then Chart.Terms, Chart.Gens, Chart.F_* (six), Chart.Main,
#      Chart.Poly, Chart.Assembly, Chart.Axioms, each with `lean -o`; any error or "declaration uses sorry" fails;
#   3. check that every `#print axioms` line of Chart/Axioms.lean names only propext, Classical.choice, Quot.sound
#      (or a subset).
# Exit status 0 iff all steps pass; 2 if the project lacks the compiled bundle or Mathlib (checked first).
# Time on 2 cores (2026-10-12): about 4 min.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
PROJ="${1:-$HERE/../bundle_v3_1/jacobian_lean}"
PROJ="$(cd "$PROJ" && pwd)" || { echo "FAIL: no Lean project at $PROJ"; exit 1; }
for f in .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean \
         .lake/build/lib/lean/Jacobian/BranchC/T1Zero/Combine.olean; do
  if [ ! -f "$PROJ/$f" ]; then
    echo "FAIL: $PROJ has no $f."
    echo "      Pass a Lake project in which the branch-(c) bundle is built (Mathlib v4.34.0 included)."
    exit 2
  fi
done
export PATH="$HOME/.elan/bin:$PATH"
OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT
mkdir -p "$OUT/GradeA/Chart" "$OUT/gen"
BASE="R67Data IrreducibleR Transfer Macaulay"
CHART="Terms Gens F_Psi F_Phi1 F_Phi2 F_Theta1 F_Theta2 F_Theta3 Main Poly Assembly Axioms"

echo "=== 0. regenerate the generated modules and compare ==="
( cd "$HERE/certgen" && PYTHONDONTWRITEBYTECODE=1 ODIR="$OUT/gen" python3 gen_chart_lean.py ) > "$OUT/gen.log" 2>&1 \
  || { echo "FAIL: gen_chart_lean.py"; cat "$OUT/gen.log"; exit 1; }
grep -E "^p = |^PASS" "$OUT/gen.log"
for m in Gens F_Psi F_Phi1 F_Phi2 F_Theta1 F_Theta2 F_Theta3 Main; do
  cmp -s "$OUT/gen/GradeA/Chart/$m.lean" "$HERE/lean/GradeA/Chart/$m.lean" \
    || { echo "FAIL: lean/GradeA/Chart/$m.lean differs from the generator's output"; exit 1; }
done
echo "PASS: the 8 generated modules are byte-identical to the generator's output"

echo "=== 1. source scan ==="
python3 - "$HERE"/lean/GradeA/*.lean "$HERE"/lean/GradeA/Chart/*.lean <<'PY' || { echo "FAIL: sorry/admit/native_decide/axiom found"; exit 1; }
import re, sys
bad = 0
for f in sys.argv[1:]:
    s = re.sub(r'/-.*?-/', '', open(f).read(), flags=re.S)
    s = re.sub(r'--[^\n]*', '', s)
    for l in s.splitlines():
        if re.search(r'\b(sorry|admit|native_decide)\b', l) or re.match(r'\s*(private\s+)?axiom\s', l):
            print(f"  {f}: {l.strip()[:120]}"); bad = 1
sys.exit(bad)
PY
echo "PASS: no sorry, admit, native_decide or axiom"

echo "=== 2. compile (project: $PROJ) ==="
cd "$PROJ" || exit 1
LP="$(lake env printenv LEAN_PATH)" || { echo "FAIL: lake env"; exit 1; }
compile() {  # $1 = module path relative to lean/GradeA (without .lean), $2 = label
  local t0=$(date +%s)
  LEAN_PATH="$OUT:$LP" lean --root="$HERE/lean" -o "$OUT/GradeA/$1.olean" "$HERE/lean/GradeA/$1.lean" \
    > "$OUT/$2.log" 2>&1
  local rc=$?
  echo "GradeA.$2: exit $rc, $(( $(date +%s) - t0 )) s"
  if [ $rc -ne 0 ] || grep -qE "error|declaration uses .sorry." "$OUT/$2.log"; then
    echo "FAIL: GradeA.$2"; head -c 4000 "$OUT/$2.log"; exit 1
  fi
}
for m in $BASE; do compile "$m" "$m"; done
for m in $CHART; do compile "Chart/$m" "Chart.$m"; done

echo "=== 3. axioms ==="
cat "$OUT/Chart.Axioms.log"
STD="(propext|Classical\.choice|Quot\.sound)"
n_all=$(grep -c "^#print axioms" "$HERE/lean/GradeA/Chart/Axioms.lean")
n_ok=$(grep -cE "depends on axioms: \[$STD(, $STD)*\][[:space:]]*$|does not depend on any axioms" "$OUT/Chart.Axioms.log")
if [ "$n_ok" -ne "$n_all" ]; then echo "FAIL: $n_ok of $n_all theorems on the standard axioms"; exit 1; fi
echo "PASS: $n_all of $n_all theorems on the standard axioms (or a subset)"
echo "=== CHART REDUCTION AND INTERFACE: ALL CHECKS PASSED ==="
