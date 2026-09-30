#!/usr/bin/env python3
"""t1z_controls.py -- G1 negative controls for the kernel-checked stratum certificate (Jacobian/BranchC/T1Zero).
Each control is a perturbed copy of a generated module, compiled standalone (no .olean written); each MUST fail.
  C1 Sq:     s_X2's target constant (Bezout c * D_O) + 1
  C2 F_Psi:  the eT1 term dropped from s_f_Psi's certificate (the slice restriction without the stratum hypothesis)
  C3 P_Psi:  one coefficient of s_p_Psi's cofactor nu_Psi changed by +1
  C4 Final:  s_final with DD + 1
  C5 Sq:     the identity s_sq with T2 = 1 not used (eT2 term dropped)
A control passes (as a control) iff lean exits nonzero with a `decide` failure message."""
import os, re, subprocess, sys, json
sys.set_int_max_str_digits(0)
# Run from the root of the Lean project (the jacobian_lean overlay applied to the branch-(a,b) project), after
# `lake build Jacobian.BranchC.T1Zero.Combine`.  JACOBIAN_LEAN overrides the root.
ROOT = os.environ.get("JACOBIAN_LEAN", os.getcwd())
S = os.path.join(ROOT, ".t1z_controls"); os.makedirs(S, exist_ok=True)
D = os.path.join(ROOT, "Jacobian/BranchC/T1Zero")
PATH = os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"]
LP = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, capture_output=True, text=True,
                    env=dict(os.environ, PATH=PATH)).stdout.strip()
env = dict(os.environ, LEAN_PATH=LP, PATH=PATH)
os.makedirs(os.path.join(S, "t1z_ctl"), exist_ok=True)
meta = json.load(open(os.path.join(ROOT, "certgen_c/t1zero_c.json")))
def run(name, txt, must):
    p = os.path.join(S, "t1z_ctl", name + ".lean"); open(p, "w").write(txt)
    r = subprocess.run(["lean", p], cwd=ROOT, env=env, capture_output=True, text=True)
    msg = (r.stdout + r.stderr)
    ok_fail = r.returncode != 0 and must in msg
    first = next((l for l in msg.splitlines() if "error" in l), "")[:160]
    print(f"{name}: exit {r.returncode}; {'FAILS AS REQUIRED' if ok_fail else 'CONTROL NOT TRIGGERED'} | {first}")
    return ok_fail
res = []
# C1
sq = open(os.path.join(D, "Sq.lean")).read()
K = int(meta["cB"]) * meta["DO"]
assert sq.count(f"(.num {K})") == 2
res.append(run("C1_Sq_bezout", sq.replace(f"(.num {K})", f"(.num {K + 1})"), "decide"))
# C2: drop eT1 from s_f_Psi's certificate list
fp = open(os.path.join(D, "F_Psi.lean")).read()
m = re.search(r"\((\(\.add .*?|\(\.mul .*?|\(\.num .*?)\), eT1\)", fp)
i = fp.index(", eT1)"); j = i
depth = 0; k = i - 1
while True:                                  # walk back to the '(' opening this pair
    c = fp[k]
    if c == ")": depth += 1
    elif c == "(":
        if depth == 0: break
        depth -= 1
    k -= 1
pair = fp[k:i + len(", eT1)")]
bad = fp.replace(pair + ", ", "", 1) if (pair + ", ") in fp else fp.replace(", " + pair, "", 1)
bad = bad.replace("h_eT1, ", "", 1)
res.append(run("C2_FPsi_drop_eT1", bad, "decide"))
# C3: perturb one nu coefficient in s_p_Psi (first numeral inside the l2 list after `f_Psi`-pair start)
pp = open(os.path.join(D, "P_Psi.lean")).read()
t = pp.index("theorem s_p_Psi")
mm = re.search(r"\(\.num \((-?\d+)\)\)", pp[pp.index("lc_zero2", t):])
s0 = pp.index("lc_zero2", t) + mm.start(1); s1 = pp.index("lc_zero2", t) + mm.end(1)
res.append(run("C3_PPsi_coeff", pp[:s0] + str(int(pp[s0:s1]) + 1) + pp[s1:], "decide"))
# C4: s_final with DD + 1 (Final.lean)
fn_ = open(os.path.join(D, "Final.lean")).read()
DD = re.search(r"\(Expr\.num (\d+)\)", fn_).group(1)
assert fn_.count(f"(Expr.num {DD})") == 2
res.append(run("C4_Final_DDplus1", fn_.replace(f"(Expr.num {DD})", f"(Expr.num {int(DD) + 1})"), "decide"))
# C5: s_sq without the chart hypothesis eT2
k = sq.index(", eT2)"); depth = 0; q = k - 1
while True:
    c = sq[q]
    if c == ")": depth += 1
    elif c == "(":
        if depth == 0: break
        depth -= 1
    q -= 1
pair = sq[q:k + len(", eT2)")]
bad = sq.replace(pair + ", ", "", 1) if (pair + ", ") in sq else sq.replace(", " + pair, "", 1)
bad = bad.replace("h_eT2, ", "", 1)
res.append(run("C5_Sq_drop_eT2", bad, "decide"))
print("controls:", "ALL FAIL AS REQUIRED" if all(res) else "SOME CONTROL NOT TRIGGERED")
