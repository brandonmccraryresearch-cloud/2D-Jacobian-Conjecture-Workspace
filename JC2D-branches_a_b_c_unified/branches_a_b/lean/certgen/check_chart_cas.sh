#!/usr/bin/env bash
# check_chart_cas.sh -- external (non-Lean) evidence for the chart system behind ChartClassification.
#
# The solutions of the chart system (a0 = b10 = 1, E_1..E_16, a7^3 b0^2 = 1) are exactly the torus
# images of the solutions with a1 = 1 plus the solutions with a1 = 0.  Mod p = 32003:
#   a1 = 0 : the ideal is the unit ideal (no solutions)            ~5 s
#   a1 = 1 : zero-dimensional, vdim 5                                ~4-5 min
# This is EVIDENCE, NOT PROOF: a count mod p does not bound the count over Q.  The exact check over Q
# (chart_system_Q.sing / chart_a1_*_Q.sing, then `python3 chart_cas.py verify chart_gb_Q.txt`) did not
# finish within this session's time limits; see CLASSIFICATION_STATUS.md.
set -euo pipefail
cd "$(dirname "$0")"
command -v Singular >/dev/null 2>&1 || { echo "SKIP: Singular not installed"; exit 0; }
o0=$(timeout 600 Singular -q chart_a1_0_p.sing); echo "$o0"
echo "$o0" | grep -q "dim -1  vdim 0" || { echo "FAIL: a1 = 0 system is not the unit ideal mod p"; exit 1; }
o1=$(timeout 3600 Singular -q chart_a1_1_p.sing); echo "$o1"
echo "$o1" | grep -q "dim 0  vdim 5" || { echo "FAIL: a1 = 1 system is not zero-dimensional of degree 5 mod p"; exit 1; }
echo "PASS (evidence only): mod 32003 the chart system has no solution with a1 = 0 and exactly 5 (with multiplicity) with a1 = 1"
