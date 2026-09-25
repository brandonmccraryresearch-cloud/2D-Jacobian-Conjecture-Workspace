"""
msolve_control.py -- positive/negative control for the msolve path of cert_fibers_msolve.py.
Requires msolve_runs/p30011_pt0_a_1_2.ms produced by `python3 cert_fibers_msolve.py 30011`.
 control: same fibre, weight-0 block dropped, a_1_2 = 1  -> must be SOLVABLE (not [-1])
 real   : all blocks,                        a_1_2 = 1  -> must be EMPTY ([-1])
"""
import subprocess, sys
from gen_system import build

LP, LQ, eqs, tgt = build()
w = lambda ij: ij[1] - 2 * ij[0]
keys = [k for k in sorted(eqs) if w(k) >= -3]          # same order as cert_fibers_msolve.py
u = "a_1_2"
res = {}
for label, drop0 in [("control_no_w0", True), ("real_full", False)]:
    lines = open(f"msolve_runs/p30011_pt0_{u}.ms").read().strip().split("\n")
    polys = "\n".join(lines[2:]).split(",\n")
    assert len(polys) == len(keys) + 1 and polys[-1].strip() == f"{u}-1"
    keep = [pp for pp, k in zip(polys[:-1], keys) if not (drop0 and w(k) == 0)] + [polys[-1]]
    fn = f"msolve_runs/{label}_{u}.ms"
    open(fn, "w").write(lines[0] + "\n" + lines[1] + "\n" + ",\n".join(keep) + "\n")
    subprocess.run(["msolve", "-f", fn, "-o", fn + ".out"], capture_output=True, text=True)
    out = open(fn + ".out").read()
    res[label] = "EMPTY" if out.startswith("[-1]") else "SOLVABLE"
    print(f"{label:14s} ({len(keep)} equations): {res[label]}   msolve: {out[:40].strip()}")
ok = res["control_no_w0"] == "SOLVABLE" and res["real_full"] == "EMPTY"
print("OVERALL:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
