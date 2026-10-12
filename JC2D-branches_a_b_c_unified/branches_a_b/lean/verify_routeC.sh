#!/usr/bin/env bash
# verify_routeC.sh -- verification of route C (Jacobian/A816C), added 2026-10-12.
#
# Route C checks the a8,16 certificate of scripts/a816_certificate/ in the Lean kernel, by reflection. Its modules
# are not imported by Jacobian.lean, so verify_branch_ab_lean.sh does not build them (its source scan for sorry,
# admit, native_decide and axiom does cover them). This script:
#   1. builds Jacobian.A816C.Bridge and Jacobian.A816C.Control.C7 (genuine exit status; fails on any
#      "declaration uses sorry");
#   2. prints the axioms of routeC_a816, routeC_source, transfer and C7_transfer_fails_without_divCtx; each must be a
#      subset of [propext, Classical.choice, Quot.sound];
#   3. runs certgen/check_routeC_statement.py (sympy): the 75 hypotheses of routeC_source are nonzero integer
#      multiples of the bracket equations of weights 3..0 of P, Q in scripts/a816_full.sing, and the conclusion is
#      a_8_16 = 0.
# What route C does not prove: routeC_source is a statement about reflected expressions, not about jac P Q for
# MvPolynomials. The link to jac is made in Python (step 3), not in Lean; route R (Jacobian/A816) is the Lean proof
# at the level of P and Q. See README.md, section 1d.
#
# Resources (2026-10-12, 2 cores, Mathlib cache and branch-(a,b) modules already built): about 34 min for step 1,
# under 2 GB of memory per module; step 3 about 25 s.
#
# Usage: verify_routeC.sh [PROJECT_DIR]   (PROJECT_DIR defaults to this script's directory)
set -u
export PATH="$HOME/.elan/bin:$PATH"
HERE="$(cd "$(dirname "$0")" && pwd)"
PROJ="${1:-$HERE}"
PY="${PYTHON:-python3}"
cd "$PROJ" || { echo "FAIL: cannot cd to $PROJ"; exit 1; }
echo "project: $PROJ"
LOG=$(mktemp)
AX=$(mktemp)
trap 'rm -f "$LOG" "$AX" "$PROJ/RouteCAxiomCheck.lean"' EXIT

echo "=== 1. lake build Jacobian.A816C.Bridge Jacobian.A816C.Control.C7 ==="
lake build Jacobian.A816C.Bridge Jacobian.A816C.Control.C7 > "$LOG" 2>&1
status=$?
grep -E "^(✔|⚠|✖) \[" "$LOG" | grep "A816C" | tail -5
echo "lake build exit status: $status"
if [ "$status" -ne 0 ]; then echo "FAIL: build errors:"; grep -E "error" "$LOG" | head -20; exit 1; fi
if grep -E "declaration uses .sorry." "$LOG"; then echo "FAIL: sorry warning in build log"; exit 1; fi
echo "PASS: build clean"

echo "=== 2. #print axioms ==="
cat > "$PROJ/RouteCAxiomCheck.lean" <<'EOF'
import Jacobian.A816C.Bridge
import Jacobian.A816C.Control.C7
#print axioms A816C.routeC_a816
#print axioms A816C.Bridge.routeC_source
#print axioms A816C.Bridge.transfer
#print axioms C7_transfer_fails_without_divCtx
EOF
lake env lean "$PROJ/RouteCAxiomCheck.lean" > "$AX" 2>&1
axstatus=$?
cat "$AX"
STD="(propext|Classical\.choice|Quot\.sound)"
n_ok=$(grep -cE "depends on axioms: \[$STD(, $STD)*\][[:space:]]*$|does not depend on any axioms" "$AX")
if [ "$axstatus" -ne 0 ] || [ "$n_ok" -ne 4 ] || grep -q sorryAx "$AX"; then
  echo "FAIL: $n_ok of 4 theorems on the standard axioms (exit $axstatus)"; exit 1
fi
echo "PASS: 4 of 4 theorems depend only on standard axioms"

echo "=== 3. statement check (certgen/check_routeC_statement.py) ==="
"$PY" "$HERE/certgen/check_routeC_statement.py"
st=$?
if [ "$st" -ne 0 ]; then echo "FAIL: statement check (exit $st)"; exit 1; fi

echo "=== ROUTE C: ALL CHECKS PASSED ==="
