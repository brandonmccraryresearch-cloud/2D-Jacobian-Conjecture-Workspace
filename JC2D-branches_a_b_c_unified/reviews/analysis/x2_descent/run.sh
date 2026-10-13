#!/bin/sh
# run.sh -- regenerate the X2 logs and compare them with the committed ones (README section 8).
#   sh run.sh          the quick runs (the m = 7 repository point, m = 3, 5, 7 and the controls; under 1 CPU-minute)
#   sh run.sh full     also m = 9 (about 4 CPU-minutes), the m = 7 run in the a1 normalization (about 11),
#                      the m = 9 Frobenius patterns at two primes (about 10) and the tree check
# Needs Singular (4.3.2 used) and python3 with sympy (for top_layer_trees.py). Exit status 1 if any log differs.
set -u
cd "$(dirname "$0")"
OUT=$(mktemp -d)
export PYTHONDONTWRITEBYTECODE=1
fail=0
run() {   # run NAME M [OPTIONS]: python3 x2_descent_rigidity.py M [OPTIONS] > OUT/NAME.log, then compare
  name=$1; shift
  python3 x2_descent_rigidity.py "$@" > "$OUT/$name.log" 2> "$OUT/$name.err"
  if cmp -s "$OUT/$name.log" "logs/$name.log"; then echo "PASS $name"; else echo "FAIL $name"; fail=1; fi
}
python3 a816_top.py ../../../branches_a_b/scripts/a816_full.sing 32003 11147 "$OUT/a816_top_32003.json" \
  > "$OUT/a816_top_32003.log"
if cmp -s "$OUT/a816_top_32003.json" logs/a816_top_32003.json && cmp -s "$OUT/a816_top_32003.log" logs/a816_top_32003.log
then echo "PASS a816_top_32003"; else echo "FAIL a816_top_32003"; fail=1; fi
run m3 3
run m5 5
run m7_control 7
run m7_negative_without_E1 7 --drop-layer 0
run m7_repository_point 7 --top logs/a816_top_32003.json
run m3_norm_a1 3 --norm a1
run m5_norm_a1 5 --norm a1
if [ "${1:-}" = full ]; then
  run m9 9 --prime 32003 --engine slimgb
  run m7_norm_a1 7 --norm a1
  python3 top_layer_galois.py 9 32003 32009 > "$OUT/galois_m9.log" 2>&1
  if cmp -s "$OUT/galois_m9.log" logs/galois_m9.log; then echo "PASS galois_m9"; else echo "FAIL galois_m9"; fail=1; fi
  python3 top_layer_trees.py > "$OUT/trees.log" 2>&1
  if cmp -s "$OUT/trees.log" logs/trees.log; then echo "PASS trees"; else echo "FAIL trees"; fail=1; fi
fi
echo "logs regenerated in $OUT"
exit $fail
