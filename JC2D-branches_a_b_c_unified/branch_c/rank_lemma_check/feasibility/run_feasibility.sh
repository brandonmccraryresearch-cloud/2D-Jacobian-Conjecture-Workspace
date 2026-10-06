#!/bin/bash
# run_feasibility.sh -- the measurements behind ../README.md, "Why packed": kernel micro-benchmarks and LU fill.
#   bash run_feasibility.sh        # about 4 min; LIST_MAX=100000 also runs the 10^5-element list benchmark, which
#                                  # needed more than 5.5 GB on 2026-10-06 and was killed
# Logs: logs/run.log (one line per step) and logs/<step>.log.
set -u
cd "$(dirname "$0")" || exit 1
HERE=$(pwd)
PY=${PY:-python3}
LEAN=${LEAN:-lean}
export PYTHONDONTWRITEBYTECODE=1
T=$(mktemp -d)
mkdir -p logs
: > logs/run.log
cp "$HERE/../../../branches_a_b/lean/lean-toolchain" "$T/lean-toolchain"
echo "run_feasibility.sh, $(date -u +%Y-%m-%dT%H:%M:%SZ); lean: $(cd "$T" && "$LEAN" --version)" >> logs/run.log
bench() {                                         # bench KIND N
  local f
  f=$("$PY" gen_kbench.py "$T" "$1" "$2")
  (cd "$T" && "$PY" "$HERE/../timed.py" "$1 $2" "$HERE/logs/kbench_$1_$2.log" "$LEAN" "$f") >> logs/run.log
}
bench loop 10000
bench loop 100000
bench list 10000
[ "${LIST_MAX:-0}" -ge 100000 ] && bench list 100000
"$PY" ../timed.py build_matrix logs/build_matrix.log "$PY" ../build_matrix.py \
  ../../bundle_v3_1/jacobian_lean/chart_certificates 32003 11147 "$T/M.pkl" 24 >> logs/run.log
"$PY" ../timed.py lu_fill logs/lu_fill.log "$PY" lu_fill.py "$T/M.pkl" >> logs/run.log
rm -rf "$T"
cat logs/run.log
