#!/usr/bin/env bash
# run_key.sh -- regenerate every log of the answer key (about 3 min on 2 cores, peak memory below 1 GB).
# DO NOT RUN THIS BEFORE YOU HAVE RECORDED YOUR OWN RESULTS (see ../INDEPENDENT_REPLICATION_GUIDE.md).
# Needs python3 with sympy and python-flint, Singular and PARI/GP on PATH. Exit status 0 iff every step passes.
set -u
cd "$(dirname "$0")"
mkdir -p logs
fail=0
step() {   # step <log> <command...>
  local log="$1"; shift
  local t0=$(date +%s)
  if "$@" < /dev/null > "logs/$log" 2>&1; then echo "ok    $log ($(( $(date +%s) - t0 )) s)"; else echo "FAIL  $log"; fail=1; fi
}
step key_checks.log  python3 key_checks.py
step field.log              gp -q field.gp
step top_layer_counts.log   Singular -q top_layer_counts.sing
step top_layer_simple.log   python3 top_layer_simple.py
step top_layer_m35.log      Singular -q top_layer_m35.sing
step descent_ideal.log      Singular -q descent_ideal.sing
step layer_consistency.log  python3 layer_consistency.py
step modp_unit_ideal.log    python3 modp_unit_ideal.py
step macaulay_rank.log      python3 macaulay_rank.py
step route_b_values.log     python3 route_b_values.py
# the Singular and PARI scripts have no pass/fail of their own: check_logs.py compares their logs with the key
step check_logs.log         python3 check_logs.py
exit $fail
