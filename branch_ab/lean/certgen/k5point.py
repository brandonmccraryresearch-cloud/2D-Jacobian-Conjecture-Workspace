"""k5point.py -- chart point of the K5 top layer in the normalization a0 = 1, b10 = 1, a7^3 b0^2 = 1 (torus), as polynomials in w mod R."""
import re, json, os, sympy as sp
HERE = os.path.dirname(os.path.abspath(__file__))
w = sp.symbols('w'); R = sp.Poly(w**5 - w**4 + 3*w**3 + 3*w**2 + 26, w, domain='QQ')
src = open(os.path.join(HERE, "..", "Jacobian", "BranchAbSharp.lean")).read()
T = {}
for line in src.splitlines():
    m = re.match(r"\s*\(t([AB])(\d+) : [AB].\.coeff (\d+) = (.*)\)$", line)
    if m:
        ex = m.group(4).replace(": L", "").replace("w ^ (", "w**(").replace(" : ℕ)", ")")
        T[(m.group(1), int(m.group(3)))] = sp.Poly(sp.sympify(ex), w, domain='QQ')
def red(p): return p.rem(R)
def inv(p):
    s, t, g = sp.gcdex(p.as_expr(), R.as_expr(), w)   # s p + t R = g
    g = sp.Poly(g, w, domain='QQ'); assert g.degree() == 0
    return red(sp.Poly(s, w, domain='QQ') * (1 / g.as_expr()))
a = {i: red(T[('A', i + 1)] * inv(T[('A', 1)])) for i in range(0, 8)}           # a0 = 1
b = {k: red(T[('B', k + 2)] * inv(T[('B', 12)])) for k in range(0, 11)}        # b10 = 1
r = red(a[7] ** 3 * b[0] ** 2)                                                   # weight-1 invariant
kT = inv(r)                                                                      # torus parameter
P = {i: red(a[i] * kT ** i) for i in range(8)}
Q = {k: red(b[k] * (kT ** k) * inv(kT ** 10)) for k in range(11)}
assert P[0] == sp.Poly(1, w, domain='QQ') and Q[10] == sp.Poly(1, w, domain='QQ')
assert red(P[7] ** 3 * Q[0] ** 2) == sp.Poly(1, w, domain='QQ')
# check the 16 bilinear equations
def coef(i, k): return 1 + 2 * k - 3 * i
for n in range(0, 18):
    s = sp.Poly(0, w, domain='QQ')
    for i in range(8):
        k = n - i
        if 0 <= k <= 10: s += coef(i, k) * P[i] * Q[k]
    s = red(s)
    assert (n == 0) or s.is_zero, (n, s)
lam = red(P[0] * Q[0])
def dig(p): return max(max(len(str(sp.fraction(c)[0])), len(str(sp.fraction(c)[1]))) for c in p.all_coeffs())
print("max digits: P", max(dig(P[i]) for i in range(8)), " Q", max(dig(Q[k]) for k in range(11)), " kT", dig(kT))
for i in range(1, 8): print(f"a{i}:", P[i].all_coeffs()[::-1][:2], "...")
json.dump({"P": {i: [str(c) for c in P[i].all_coeffs()[::-1]] for i in range(8)},
           "Q": {k: [str(c) for c in Q[k].all_coeffs()[::-1]] for k in range(11)},
           "kT": [str(c) for c in kT.all_coeffs()[::-1]]}, open(os.path.join(HERE, "chartpoint.json"), "w"), indent=0)
print("written chartpoint.json")
