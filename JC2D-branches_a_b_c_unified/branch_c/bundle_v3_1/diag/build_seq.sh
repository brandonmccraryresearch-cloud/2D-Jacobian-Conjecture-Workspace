#!/usr/bin/env bash
# build_seq.sh MODULE... : `lake build -v` each module in turn (one lean process at a time), under the memory guard.
# VERBOSE: the complete, unfiltered lake/lean output of every module goes to buildlogs/<module>.log and is also echoed
# into this script's log; the guard prints a status line (elapsed, peak RSS, cgroup anon) every 10 s.
cd /home/claude/build/jacobian_lean
export PATH="$HOME/.elan/bin:$PATH"
S=/tmp/claude-0/-home-claude-2d-jacobian-conjecture-workspace/3a473603-c1a6-574c-94db-ab1d05a9f323/scratchpad
mkdir -p $S/buildlogs
for m in "$@"; do
  f=$S/buildlogs/$m.log
  echo "== $m  $(date '+%F %T')  (full log: $f)"
  python3 $S/guardrun.py --verbose --max-anon 5600 -- lake build -v "$m" > "$f" 2>&1
  rc=$?
  cat "$f"
  if [ $rc -ne 0 ]; then echo "FAILED $m  $(date '+%F %T')  exit $rc"; exit 1; fi
  echo "OK $m  $(date '+%F %T')"
done
echo "ALL OK $(date '+%F %T')"
