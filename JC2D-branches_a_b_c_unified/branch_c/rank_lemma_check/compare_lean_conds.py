"""compare_lean_conds.py -- a second, cheaper check of premise H6 (README.md), modulo p at random points.

On the chart (T2 = b_12_22 = 1, S2 = b_12_23 = kappa) at a root w0 of R mod p, compare
    cond_n(w0, t, 1, s, kappa, r, u, q)       (CondsC.lean, parsed from its own text)
    F_n(t, s, r, u, q)                         (the generators of the rank computation, step3b_rank_lift.py)
for n = Psi, Phi1, Phi2, Theta1, Theta2, Theta3 at NPTS random points: the ratio must be one nonzero constant per n.
Also cond_Omega must vanish at S2 = kappa at every point and be nonzero at S2 = kappa + 1.
Control: with S2 = kappa + 1 the ratios must not all be constant.
usage: python3 compare_lean_conds.py CondsC.lean CHART_CERTIFICATES_DIR p w0 NPTS      (needs python-flint)
"""
import sys, os, re, random

LEAN, CH, p, w0, NPTS = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
sys.set_int_max_str_digits(0)
sys.path.insert(0, CH)
sys.path.insert(0, os.path.join(CH, "step1"))
import step3b_rank_lift as S                     # read-only; run with PYTHONDONTWRITEBYTECODE=1

ARGS = "w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21"
src = open(LEAN).read()
defs = re.findall(r"noncomputable def (cond_\w+) \(" + ARGS + r" : L\) : L :=\n(.*?)\n\n", src, re.S)
assert len(defs) == src.count("noncomputable def")
code = {}
for name, body in defs:
    e = re.sub(r"\((-?\d+) : L\)", r"(\1)", body.strip())
    e = re.sub(r"(cond_\w+) " + ARGS, r"V['\1']", e).replace("^", "**")
    code[name] = compile(e, name, "eval")
C7 = S.load7()
kap = S.kappa(C7)
red = S.reducer(p, w0)                           # asserts R(w0) = 0 mod p and p-integrality
kp = red(kap)
ch = S.chart(C7, kap)
G = {n: {m: red(c) for m, c in ch[n].items()} for n in S.NAMES}


def evalG(n, pt):
    t, s, r, u, q = pt
    return sum(c * pow(t, a, p) * pow(s, b, p) * pow(r, cc, p) * pow(u, d, p) * pow(q, e, p)
               for (a, b, cc, d, e), c in G[n].items()) % p


def evalLean(pt, S2):
    t, s, r, u, q = pt
    V = {}
    env = {"w": w0, "b_11_20": t, "b_12_22": 1, "b_11_21": s, "b_12_23": S2, "a_6_13": r, "a_7_15": u,
           "b_10_21": q, "V": V}
    for name, _ in defs:
        V[name] = eval(code[name], {}, env) % p
    return V


rng = random.Random(20261006)
ratios = {n: set() for n in S.NAMES}
ratios_bad = {n: set() for n in S.NAMES}
omega0, omega1 = set(), set()
for _ in range(NPTS):
    pt = tuple(rng.randrange(1, p) for _ in range(5))
    V, Vb = evalLean(pt, kp), evalLean(pt, (kp + 1) % p)
    for n in S.NAMES:
        g = evalG(n, pt)
        ratios[n].add(V["cond_" + n] * pow(g, -1, p) % p if g else None)
        ratios_bad[n].add(Vb["cond_" + n] * pow(g, -1, p) % p if g else None)
    omega0.add(V["cond_Omega"])
    omega1.add(Vb["cond_Omega"] != 0)
ok = True
print(f"p = {p}, w0 = {w0}, kappa mod p = {kp}, {NPTS} random points (seed 20261006)")
for n in S.NAMES:
    r = ratios[n]
    good = len(r) == 1 and None not in r and 0 not in r
    print(f"  {n:7s} cond_{n} / F_{n}: {'constant ' + str(next(iter(r))) if good else 'NOT CONSTANT ' + str(sorted(r, key=str)[:3])}")
    ok &= good
print(f"  cond_Omega at S2 = kappa: values {sorted(omega0)} (must be [0]); nonzero at S2 = kappa + 1 at every point: "
      f"{omega1 == {True}}")
ok &= omega0 == {0} and omega1 == {True}
bad_rejected = any(len(ratios_bad[n]) > 1 for n in S.NAMES)
print(f"control: S2 = kappa + 1 -> some ratio not constant: {bad_rejected} (must be True)")
ok &= bad_rejected
print("ALL RATIOS CONSTANT; CONTROL REJECTED" if ok else "CHECK FAILED")
sys.exit(0 if ok else 1)
