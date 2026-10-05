#!/bin/bash
# verify_bundle.sh -- exact checks of the two a_{8,16} certificates in this directory (about 2 minutes).
# Needs Singular >= 4.3 and Python 3 with python-flint 0.9 (and sympy for the B2.6 check).
# Source of P and Q: the repository file ../a816_full.sing if present, else the copy here
# (both must have md5 aa68d2ffa08a8db86627a03e41f4e94d).  Set A816_SRC to override.
set -u
cd "$(dirname "$0")"
REPO_SRC="$PWD/../a816_full.sing"          # scripts/a816_full.sing in the repository
if [ -z "${A816_SRC:-}" ]; then if [ -f "$REPO_SRC" ]; then A816_SRC=$REPO_SRC; else A816_SRC=$PWD/a816_full.sing; fi; fi
export A816_SRC
fail=0
echo "source of P, Q: $A816_SRC"; m=$(md5sum < "$A816_SRC" | cut -d' ' -f1); echo "md5 $m"
[ "$m" = aa68d2ffa08a8db86627a03e41f4e94d ] || { echo "WRONG SOURCE FILE"; fail=1; }
CERTS="a816_lift.txt"
if [ -f a816_lift_liftstd.txt ]; then CERTS="$CERTS a816_lift_liftstd.txt"
else echo "(a816_lift_liftstd.txt not present: it is not committed to the repository; see README.md section 2)"; fi
for f in $CERTS; do
  echo "== python-flint (independent rebuild of J): $f"; python3 verify_cert_flint.py $f gens_0.txt | grep -E "certificate:|RESULT|time"; r=${PIPESTATUS[0]}; echo "exit $r"; [ $r -eq 0 ] || fail=1
done
for c in perturb drop_rabinowitsch wrong_minpoly; do
  echo "== negative control on a816_lift.txt: $c (must be rejected)"; python3 verify_cert_flint.py a816_lift.txt gens_0.txt --control $c | grep RESULT; r=${PIPESTATUS[0]}; echo "exit $r"; [ $r -eq 1 ] || fail=1
done
for f in $CERTS; do
  echo "== Singular over Q(w), repository generators: $f"; python3 mk_check_lift.py $f check_$f.sing > /dev/null
  out=$(Singular -q check_$f.sing 2>&1); echo "$out" | grep -E "SINGULAR CHECK"; echo "$out" | grep -q "VALID" || fail=1; rm -f check_$f.sing
done
echo "== round trip with CAIC's a816_generators.txt (caic_inputs/)"; python3 mk_aux_sing.py > /dev/null
out=$(Singular -q check_roundtrip.sing 2>&1); echo "$out" | grep -E "ROUND TRIP"; echo "$out" | grep -q "VALID" || fail=1
out=$(Singular -q cmp_gens.sing 2>&1); echo "CAIC generators vs repository ideal, entrywise mismatches: $(echo "$out" | tail -1)"; [ "$(echo "$out" | tail -1)" = 0 ] || fail=1
rm -f check_roundtrip.sing
echo "== B2.6 eliminant checks"; python3 b26_check.py | grep -E "factor_list|disc_u|irreducible mod"
echo "== overall: $([ $fail -eq 0 ] && echo ALL CHECKS PASSED || echo SOMETHING FAILED)"
exit $fail
