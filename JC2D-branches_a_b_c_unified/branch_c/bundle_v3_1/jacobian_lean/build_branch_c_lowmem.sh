#!/usr/bin/env bash
# build_branch_c_lowmem.sh -- build the branch-(c) modules and all their Jacobian.* dependencies ONE AT A TIME.
#
# Why: `lake build` (Lake 5.0 / Lean 4.34.0 has no -j option) runs one lean process per core, and single modules
# of this project are large.  Peak resident memory (RSS) and heap of the lean process for one module (lean 4.34.0,
# x86-64 Linux, 2 cores, 8 GB, no swap; /proc/<pid>/smaps_rollup).  RSS minus heap is mostly memory-mapped .olean
# files, shared between concurrent lean processes; the heap is private.
#                                                                  RSS     heap    time
#     Jacobian/Descent/E3/x_* (branch a,b), `import Mathlib`        5.0 GB  1.6 GB  39 s
#       the same after lighten_ab_descent_imports.py                2.7 GB  1.3 GB  25 s
#     (a,b) modules importing all of Mathlib anyway
#       (Descent.Main, ChartProof.Final, BranchAb*)                 4.7-5.1 0.4-0.9 25-80 s
#     BranchC/DescentClaim (imports ChartProof.Final)               5.0 GB  0.45 GB 25 s
#     BranchC/Descent/Omega1                                        4.3 GB  3.1 GB  65 s
#     BranchC/Descent/E1red/* (largest)                             3.8 GB  2.4 GB  50 s
#     BranchC/Descent/MainOmega (E3 lightened; 5.2 GB RSS if not)   2.2 GB  0.7 GB  29 s
#     BranchC/Rank/*/piv_* (largest)                                2.4 GB  1.1 GB  20 s
#     the lake process itself                                       0.9 GB  0.2 GB
# Sequential: about 6 GB RSS at worst (fits in 7 GB).  Parallel on 2 cores: two full-Mathlib modules (~3.3-4.4 GB
# shared + two heaps + lake) thrash on 7 GB, and Omega1 next to an E1red module needs 5.5 GB of heap alone.
#
# Usage:  ./build_branch_c_lowmem.sh                 # every module under Jacobian/BranchC (+ dependencies)
#         ./build_branch_c_lowmem.sh Jacobian.BranchC.Descent.MainOmega Jacobian.BranchC.DescentClaim
# If everything is already built, one `lake build --no-build` call says so (seconds); otherwise each module is
# passed to lake separately (about 1.5 s per up-to-date module) and each module actually built is reported.
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
ORDER=$(mktemp); LOG=$(mktemp); trap 'rm -f "$ORDER" "$LOG"' EXIT
python3 - "$@" > "$ORDER" <<'PY'
import os, re, sys
tops = sys.argv[1:]
if not tops:
    for d, _, fs in os.walk("Jacobian/BranchC"):
        for f in sorted(fs):
            if f.endswith(".lean"):
                tops.append(os.path.join(d, f)[:-5].replace("/", "."))
order, seen = [], set()
def visit(m):
    if m in seen:
        return
    seen.add(m)
    p = m.replace(".", "/") + ".lean"
    if not os.path.exists(p):
        sys.exit(f"missing source for {m}: {p}")
    for line in open(p):
        mm = re.match(r"\s*import\s+(Jacobian\S*)", line)
        if mm:
            visit(mm.group(1))
    order.append(m)
sys.setrecursionlimit(10000)
for t in sorted(tops):
    visit(t)
print("\n".join(order))
PY
n=$(wc -l < "$ORDER"); i=0; t0=$(date +%s)
# fast path: one lake call decides whether anything needs building at all (`--no-build` exits non-zero if so)
if lake build --no-build $(cat "$ORDER") > "$LOG" 2>&1; then
  echo "all $n modules are up to date ($(( $(date +%s) - t0 ))s)"; exit 0
fi
while read -r m; do
  i=$((i + 1))
  # run `lake build $m`; report wall time and the peak resident memory of the largest child (the lean process)
  if ! python3 - "$m" > "$LOG" 2>&1 <<'PY'
import resource, subprocess, sys, time
t = time.time()
r = subprocess.run(["lake", "build", sys.argv[1]], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
print(r.stdout)
print(f"__stats__ {round(time.time() - t)}s, peak {resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss // 1024} MB")
sys.exit(r.returncode)
PY
  then
    echo "[$i/$n] $m  FAILED"; cat "$LOG"; exit 1
  fi
  if grep -q "Built $m" "$LOG"; then echo "[$i/$n] $m  built ($(grep -o '__stats__.*' "$LOG" | cut -d' ' -f2-))"; fi
done < "$ORDER"
echo "done: $n modules checked/built in $(( $(date +%s) - t0 ))s"
