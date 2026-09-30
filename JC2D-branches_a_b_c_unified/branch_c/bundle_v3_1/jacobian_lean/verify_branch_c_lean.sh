#!/usr/bin/env bash
# verify_branch_c_lean.sh -- rebuild and audit the branch-(c) Lean formalization.
#   1. regenerate the certificate data and generated Lean from scratch copies of the generators and compare
#      byte-for-byte with the shipped files (certgen_c/*.py; inputs certgen/cert.json, certgen/e5_exact_K5.json,
#      certgen/gen_system.py, certgen_c/omega_pipeline.json);
#   2. lake build every branch-(c) module;
#   3. #print axioms on every named theorem (only propext / Classical.choice / Quot.sound allowed);
#   4. grep: no `sorry`, no `axiom`, no `native_decide` in Jacobian/BranchC.
# Requires: elan/lake (Lean 4 + Mathlib v4.34.0 as in lake-manifest.json), python3 with python-flint and sympy.
# Memory: single modules peak at up to 5.2 GB (see build_branch_c_lowmem.sh).  With less than 12 GB available
# (or LOWMEM=1) step 2 builds one module at a time; LOWMEM=0 forces lake's parallel build.
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
echo "== 0. prerequisites (the branch-(a,b) project this overlay builds on)"
for f in certgen/cert.json certgen/e5_exact_K5.json certgen/gen_system.py Jacobian/Descent/E4/z_a_1_1.lean \
         Jacobian/Descent/E3red/r3_1_0.lean Jacobian/Descent/E3/x_a_1_2.lean Jacobian/ChartProof/Final.lean \
         Jacobian/BranchAbChart.lean Jacobian/BranchAbTorus.lean Jacobian/BranchAbNewton.lean; do
  [ -f "$f" ] || { echo "FAIL: missing $f (the overlay needs the full branch-(a,b) jacobian_lean project)"; exit 1; }
done
python3 - <<'PY'
import hashlib, glob, sys
def body(f, strip_imports):
    # The Descent fingerprint ignores the leading import block: the repository files say `import Mathlib`, and
    # lighten_ab_descent_imports.py may have replaced that by four specific Mathlib imports.  Everything after
    # the import block (statements and proofs) must match exactly.
    lines = open(f, "rb").read().split(b"\n")
    i = 0
    while strip_imports and i < len(lines) and (not lines[i].strip() or lines[i].lstrip().startswith(b"import ")):
        i += 1
    return b"\n".join(lines[i:])
def h(files, strip_imports=False):
    m = hashlib.sha256()
    for f in sorted(files):
        m.update(f.encode()); m.update(body(f, strip_imports))
    return m.hexdigest()[:16]
descent = glob.glob("Jacobian/Descent/E4/*.lean") + glob.glob("Jacobian/Descent/E3red/*.lean") + glob.glob("Jacobian/Descent/E3/*.lean")
got = {"certgen inputs": h(["certgen/cert.json", "certgen/e5_exact_K5.json", "certgen/gen_system.py"]),
       "Descent E4/E3red/E3 sources (imports ignored)": h(descent, strip_imports=True)}
# expected values = branch_ab_v17/lean (and the v19 Lean tree) of the repository, 54 Descent files
want = {"certgen inputs": "442bf8d1f27248f0", "Descent E4/E3red/E3 sources (imports ignored)": "260a235be1028994"}
if len(descent) != 54: sys.exit(f"FAIL: expected 54 Descent E4/E3red/E3 files, found {len(descent)}")
bad = [k for k in want if got[k] != want[k]]
for k in want: print(f"  {k}: {got[k]}  (expected {want[k]})")
if bad:
    sys.exit("FAIL: prerequisite fingerprint mismatch -- the branch-(a,b) files differ from the ones the generated "
             "branch-(c) chain was built against: " + ", ".join(bad))
print("PASS: prerequisite fingerprints match")
PY
echo "== 1. regeneration"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mkdir -p "$T/Jacobian/BranchC"; cp -r certgen "$T/certgen"; cp -r certgen_c "$T/certgen_c"
cp Jacobian/BranchC/*.lean "$T/Jacobian/BranchC/" 
(cd "$T/certgen_c" && python3 make_cert_c.py > make_cert_c.log && python3 gen_omega_edge.py > /dev/null \
   && python3 gen_lean_c.py > /dev/null && python3 gen_rank_c.py > rank.log)
tail -3 "$T/certgen_c/make_cert_c.log"; cat "$T/certgen_c/rank.log"
cmp "$T/certgen_c/cert_c.json" certgen_c/cert_c.json
diff -r "$T/Jacobian/BranchC/Descent" Jacobian/BranchC/Descent
diff -r "$T/Jacobian/BranchC/Rank" Jacobian/BranchC/Rank
# v3: the reflective chain E4..E-2 (Descent2R), Bridge, the named conditions (CondsC), the stratum t1 = 0 (T1Zero)
if [ "${SKIP_REFL_REGEN:-0}" != 1 ]; then
  mkdir -p "$T/chart_certificates/step1"; cp chart_certificates/step1/certB_lowerc.json "$T/chart_certificates/step1/"
  (cd "$T/certgen_c" && WRITE=1 python3 gen_refl_c.py > refl.log && python3 gen_bridge_c.py > bridge.log \
     && python3 gen_conds_c.py > conds.log && python3 gen_t1zero_lean.py > t1zero.log && python3 gen_t1zero_combine.py > combine.log)
  tail -1 "$T/certgen_c/refl.log"; tail -2 "$T/certgen_c/t1zero.log"
  cmp "$T/certgen_c/bridge_c.json" certgen_c/bridge_c.json
  diff -r "$T/Jacobian/BranchC/Descent2R" Jacobian/BranchC/Descent2R
  diff "$T/Jacobian/BranchC/CondsC.lean" Jacobian/BranchC/CondsC.lean
  diff -r "$T/Jacobian/BranchC/T1Zero" Jacobian/BranchC/T1Zero
fi
echo "PASS: regenerated certificate data and generated Lean are byte-identical"
echo "== 2. build"
avail_kb=$(awk '/MemAvailable/ {print $2}' /proc/meminfo 2>/dev/null || echo 0); avail_kb=${avail_kb:-0}
# a memory cgroup limit (v1 or v2) below MemAvailable is the real constraint (it is what the OOM killer enforces)
for f in /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory/memory.limit_in_bytes \
         "/sys/fs/cgroup/memory$(awk -F: '$2=="memory" {print $3}' /proc/self/cgroup 2>/dev/null)/memory.limit_in_bytes"; do
  if [ -r "$f" ]; then v=$(cat "$f"); case "$v" in ''|max|*[!0-9]*) ;; *) [ $((v / 1024)) -lt "$avail_kb" ] && avail_kb=$((v / 1024));; esac; fi
done
if [ "${LOWMEM:-auto}" = 1 ] || { [ "${LOWMEM:-auto}" = auto ] && [ "$avail_kb" -lt 12000000 ]; }; then
  echo "  sequential build (MemAvailable ${avail_kb} kB; LOWMEM=${LOWMEM:-auto})"
  ./build_branch_c_lowmem.sh
else
  lake build Jacobian.BranchC.Degree19 Jacobian.BranchC.LayerE2 Jacobian.BranchC.LayersGen Jacobian.BranchC.Edge19 \
    Jacobian.BranchC.OmegaSquare Jacobian.BranchC.OmegaEdge Jacobian.BranchC.DescentClaim \
    Jacobian.BranchC.Descent.MainOmega Jacobian.BranchC.Rank.E2.Kernel Jacobian.BranchC.Rank.E1.Kernel Jacobian.BranchC.Rank.E0.Kernel \
    Jacobian.BranchC.Rank.Em1.Kernel Jacobian.BranchC.Rank.Em2.Kernel Jacobian.BranchC.Rank.E2.lnull Jacobian.BranchC.Rank.E1.lnull Jacobian.BranchC.Rank.E0.lnull Jacobian.BranchC.Rank.Em1.lnull Jacobian.BranchC.Rank.Em2.lnull \
    Jacobian.BranchC.CondsC Jacobian.BranchC.T1Zero.Combine 2>&1 | tail -2
fi
echo "== 3. axioms"
lake env lean AxiomsAuditBranchC.lean > axioms_branch_c.log 2>&1
cat axioms_branch_c.log
if grep -v "^'" axioms_branch_c.log | grep -q .; then echo "FAIL: unexpected output"; exit 1; fi
if grep "depends on axioms" axioms_branch_c.log | grep -v "\[propext, Classical.choice, Quot.sound\]\|\[propext, Quot.sound\]\|\[propext\]\|\[Classical.choice, propext, Quot.sound\]" | grep -q .; then
  echo "FAIL: non-standard axiom"; exit 1; fi
echo "PASS: every audited theorem uses only the standard axioms"
echo "== 4. grep"
# (docstrings may say "no `native_decide`" in backquotes, as they may say `sorry`; only unquoted uses count)
if grep -rnE "^\s*(private\s+)?axiom\s" Jacobian/BranchC --include=*.lean; then echo "FAIL: axiom"; exit 1; fi
if grep -rn "native_decide" Jacobian/BranchC --include=*.lean | grep -v '`native_decide`'; then echo "FAIL: native_decide"; exit 1; fi
if grep -rnw "sorry" Jacobian/BranchC --include=*.lean | grep -v '`sorry`'; then echo "FAIL: sorry"; exit 1; fi
echo "PASS: no sorry / axiom / native_decide in Jacobian/BranchC"
