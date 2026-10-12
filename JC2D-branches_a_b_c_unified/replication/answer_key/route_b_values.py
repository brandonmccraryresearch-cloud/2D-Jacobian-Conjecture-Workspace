"""
route_b_values.py -- answer key C3, route B: evaluate the Lean conditions of CondsC.lean themselves.

DO NOT READ OR RUN THIS BEFORE YOU HAVE RECORDED YOUR OWN RESULTS (see ../INDEPENDENT_REPLICATION_GUIDE.md).

Input: branch_c/bundle_v3_1/jacobian_lean/Jacobian/BranchC/CondsC.lean (the twelve conditions that
`ChartEmptyC_T1ne0` quantifies over). Each `noncomputable def cond_X (w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15
b_10_21 : L) : L := ...` is translated mechanically into a Python function over the integers: numerals `(N : L)`
become N, `^` becomes `**`, and calls of subtree definitions keep their eight arguments. Then, modulo p:
  - Omega vanishes at b_12_23 = kappa b_12_22^2 for random values of the other arguments (kappa = kappa mod p);
  - the route-B values F_n(1, 2, 3, 4, 5) = cond_n(w0, t=1, b_12_22=1, s=2, b_12_23=kappa, r=3, u=4, q=5) mod p.
They are the route-A values times the positive integer by which each Lean condition is scaled.
Run: python3 route_b_values.py   (about 1 s)
"""
import os, re, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
UNI = os.path.abspath(os.path.join(HERE, "..", ".."))
LEAN = os.path.join(UNI, "branch_c", "bundle_v3_1", "jacobian_lean", "Jacobian", "BranchC", "CondsC.lean")
ARGS = "w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21"
src = open(LEAN).read()
defs = re.findall(r"noncomputable def (cond_\w+) \(" + ARGS + r" : L\) : L :=\n(.*?)(?=\n\n|\n/--|\nend)", src, re.S)
env = {}
code = []
for name, body in defs:
    b = re.sub(r"\((-?\d+) : L\)", r"(\1)", body)
    b = re.sub(r"(cond_\w+) " + ARGS, lambda m: m.group(1) + "(" + ARGS.replace(" ", ", ") + ")", b)
    b = b.replace("^", "**")
    assert re.fullmatch(r"[\sA-Za-z0-9_(),+*\-]*", b), name
    code.append(f"def {name}({ARGS.replace(' ', ', ')}):\n    return {b.strip()}\n")
exec("\n".join(code), env)
names = [n for n, _ in defs if not re.search(r"_c\d+$", n)]
print(f"{len(defs)} definitions translated; conditions: {names}")
ok = [0, 0]
def check(cond, label, value):
    print(("PASS  " if cond else "FAIL  ") + f"{label}: {value}")
    ok[0 if cond else 1] += 1
check(len(defs) == 110 and len(names) == 12, "CondsC.lean: 110 definitions, 12 conditions", (len(defs), len(names)))
SIX = ["Psi", "Phi1", "Phi2", "Theta1", "Theta2", "Theta3"]
WANT = {32003: (11147, 2737, [12299, 5562, 26403, 9106, 14593, 18204]),
        1000003: (806739, 993853, [858748, 624037, 277344, 197562, 721531, 531493])}
for p, (w0, kap, want) in WANT.items():
    rnd = random.Random(p)
    zero = True
    for _ in range(5):
        x = [rnd.randrange(p) for _ in range(7)]          # b_11_20, b_12_22, b_11_21, -, a_6_13, a_7_15, b_10_21
        x[3] = kap * x[1] * x[1] % p                      # b_12_23 = kappa b_12_22^2
        zero &= env["cond_Omega"](w0, *x) % p == 0
    check(zero, f"mod {p}: Lean cond_Omega vanishes at b_12_23 = kappa b_12_22^2 (5 random points)", zero)
    off = env["cond_Omega"](w0, 1, 1, 2, (kap + 1) % p, 3, 4, 5) % p
    check(off != 0, f"mod {p}: control, cond_Omega at b_12_23 = (kappa + 1) b_12_22^2 is nonzero", off)
    vals = [env["cond_" + n](w0, 1, 1, 2, kap, 3, 4, 5) % p for n in SIX]
    check(vals == want, f"mod {p}: route-B F_n(1,2,3,4,5) (Psi, Phi1, Phi2, Theta1, Theta2, Theta3)", vals)
print(f"ROUTE B CHECKS: {ok[0]} passed, {ok[1]} failed")
sys.exit(1 if ok[1] else 0)
