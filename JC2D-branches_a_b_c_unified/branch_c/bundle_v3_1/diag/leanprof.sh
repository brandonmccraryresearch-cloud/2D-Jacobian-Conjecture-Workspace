#!/usr/bin/env bash
# leanprof.sh FILE.lean [THRESHOLD_MS] -- compile one Lean file (no .olean written) under the memory guard with Lean's
# profiler on; print the slowest steps and the cumulative categories (elaboration, typeclass inference, kernel type
# checking, tactic execution, ...).  Run from the root of the Lean project (or set JACOBIAN_LEAN).
set -uo pipefail
D=$(cd "$(dirname "$0")" && pwd)
F=$(realpath "$1"); TH=${2:-500}
cd "${JACOBIAN_LEAN:-$PWD}"
export PATH="$HOME/.elan/bin:$PATH"; export LEAN_PATH=$(lake env printenv LEAN_PATH)
OUT=$(mktemp)
python3 "$D/guardrun.py" --max-anon ${MAX_ANON:-5300} -- lean -Dprofiler=true -Dprofiler.threshold=$TH "$F" > "$OUT" 2>&1
echo "== slowest steps (>= ${TH} ms)"; grep -E " took [0-9.]+(ms|s)$" "$OUT" | sed -E 's/^(.{0,150}).*( took .*)$/\1 …\2/' |
  awk '{t=$NF; v=t+0; if (t ~ /ms$/) v=v/1000; printf "%9.2fs  %s\n", v, $0}' | sort -rn | head -15 | cut -c1-200
echo "== cumulative"; sed -n '/cumulative profiling times/,$p' "$OUT" | grep -v guardrun
grep -E "error|guardrun" "$OUT" | head -5
rm -f "$OUT"
