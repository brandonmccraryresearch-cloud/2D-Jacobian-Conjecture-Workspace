#!/bin/bash
# run.sh -- the branch-(c) rank-lemma checks of README.md.  Reads the v3.1 bundle; writes nothing into it.
#   bash run.sh                    # about 9 min on 2 cores; about 200 MB of temporary disk
#   PY=/path/to/python bash run.sh # a Python with python-flint and numpy (scipy optional), e.g. the `physics` env
#   JOBS=1 bash run.sh             # one Lean process at a time (each peaks at about 1.9 GB)
#   KEEP=DIR bash run.sh           # keep the generated Lean files and .olean files in DIR
# Logs: logs/run.log (one line per step), logs/<step>.log, logs/lean/<module>.log, and logs/MANIFEST.sha256 (the
# sha256 of every generated Lean file; a rerun must reproduce it byte for byte).
set -u
cd "$(dirname "$0")" || exit 1
HERE=$(pwd)
PY=${PY:-python3}
LEAN=${LEAN:-lean}
JOBS=${JOBS:-2}
K=8
BUNDLE=$HERE/../bundle_v3_1/jacobian_lean
CHART=$BUNDLE/chart_certificates
CONDS=$BUNDLE/Jacobian/BranchC/CondsC.lean
TOOLCHAIN=$HERE/../../branches_a_b/lean/lean-toolchain
export PYTHONDONTWRITEBYTECODE=1                  # never write __pycache__ into the bundle
T=$(mktemp -d)
LEANDIR=${KEEP:-$T/lean}
mkdir -p "$LEANDIR" logs/lean
LEANDIR=$(cd "$LEANDIR" && pwd)
status=0
: > logs/run.log
note() { echo "$*" >> logs/run.log; }
run() {                                           # run STEP cmd ...: output in logs/STEP.log, summary in run.log
  local step=$1; shift
  "$PY" timed.py "$step" "logs/$step.log" "$@" >> logs/run.log || status=1
}
note "run.sh, $(date -u +%Y-%m-%dT%H:%M:%SZ); $("$PY" -c 'import sys, flint, numpy; print("python", sys.version.split()[0], "| python-flint", flint.__version__, "| numpy", numpy.__version__)')"

# premises H3 and H6 (README.md), and the matrix, the inverse and the Lean files
run check_R "$PY" check_R.py
run exact_lean_vs_json "$PY" exact_lean_vs_json.py "$CONDS" "$CHART"
run compare_lean_conds_32003 "$PY" compare_lean_conds.py "$CONDS" "$CHART" 32003 11147 20
run compare_lean_conds_1000003 "$PY" compare_lean_conds.py "$CONDS" "$CHART" 1000003 806739 20
run build_matrix "$PY" build_matrix.py "$CHART" 32003 11147 "$T/M.pkl" 24
run make_inverse "$PY" make_inverse.py "$T/M.pkl" "$T/inv.pkl"
rm -f "$T/M.pkl"
run gen_lean "$PY" gen_lean.py "$T/inv.pkl" "$LEANDIR" "$K"
rm -f "$T/inv.pkl"
if [ ! -f "$LEANDIR/MANIFEST.sha256" ]; then
  note "generated Lean files: MISSING"; status=1
elif [ ! -f logs/MANIFEST.sha256 ]; then
  cp "$LEANDIR/MANIFEST.sha256" logs/MANIFEST.sha256; note "generated Lean files: logs/MANIFEST.sha256 written (first run)"
elif cmp -s "$LEANDIR/MANIFEST.sha256" logs/MANIFEST.sha256; then
  note "generated Lean files: byte-identical to logs/MANIFEST.sha256"
else
  note "generated Lean files: DIFFER from logs/MANIFEST.sha256"; status=1
fi

# the kernel check: core Lean only (no Mathlib), at the toolchain pinned for the repository
cp "$TOOLCHAIN" "$LEANDIR/lean-toolchain"
note "lean: $(cd "$LEANDIR" && "$LEAN" --version)"
lean_mod() {
  (cd "$LEANDIR" && LEAN_PATH="$LEANDIR" "$PY" "$HERE/timed.py" "$1" "$HERE/logs/lean/$1.log" \
     "$LEAN" --root=. -o "$1.olean" "$1.lean") >> logs/run.log
}
build() {                                         # build MODULE ..., at most JOBS at a time
  for m in "$@"; do
    while [ "$(jobs -rp | wc -l)" -ge "$JOBS" ]; do sleep 1; done
    lean_mod "$m" &
  done
  wait
}
build RCCommon
build $(for k in $(seq 0 $((K - 1))); do printf 'RCData%02d ' "$k"; done)
build $(for k in $(seq 0 $((K - 1))); do printf 'RCCheck%02d ' "$k"; done)
build RCControls                                  # exits 1 by design: five statements must be rejected
run check_logs "$PY" check_logs.py "$LEANDIR" logs/lean "$K"
rm -rf "$T"
grep '^RESULT' logs/check_logs.log
echo "run.sh: exit $status (details in logs/run.log)"
exit $status
