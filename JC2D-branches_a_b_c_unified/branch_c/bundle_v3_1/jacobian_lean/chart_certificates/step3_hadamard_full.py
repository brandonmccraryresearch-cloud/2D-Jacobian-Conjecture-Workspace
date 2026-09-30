"""Hadamard bound for the full-chart canonical certificate (weight 24): pivots of the K5 system at a root mod p,
each pivot column expanded to its 5 w-shifts (w^j * m * F_i, j = 0..4) and integerised."""
import sys, os, math, time
sys.path.insert(0, os.path.abspath(".")); sys.path.insert(0, os.path.abspath("step1"))
from lowerc_chart import *
from flint import nmod_mat, fmpq
from fractions import Fraction as Fr
C7 = load7(); kap = kappa(C7); ch = chart(C7, kap)
WTF = {"Psi": 5, "Phi1": 6, "Phi2": 6, "Theta1": 7, "Theta2": 7, "Theta3": 7}
def monos_upto(W):
    out = []
    for t in range(W + 1):
        for s in range((W - t) // 2 + 1):
            for r in range((W - t - 2 * s) // 3 + 1):
                for u in range((W - t - 2 * s - 3 * r) // 3 + 1):
                    for q in range((W - t - 2 * s - 3 * r - 3 * u) // 4 + 1):
                        out.append((t, s, r, u, q))
    return out
p, w0 = 1000003, 806739
def red(a):
    t = 0
    for k, c in enumerate(a.coeffs()):
        f = Fr(str(c)); t = (t + f.numerator * pow(f.denominator, -1, p) * pow(w0, k, p)) % p
    return t
W = 24
cols = [(n, m) for n in NAMES for m in monos_upto(W - WTF[n])]
rows = {}
for n, m in cols:
    for mm in ch[n]: rows.setdefault(tuple(a + b for a, b in zip(m, mm)), len(rows))
A = nmod_mat(len(rows), len(cols), p)
G = {n: {mm: red(c) for mm, c in ch[n].items()} for n in NAMES}
for j, (n, m) in enumerate(cols):
    for mm, c in G[n].items():
        if c: A[rows[tuple(a + b for a, b in zip(m, mm))], j] = c
t0 = time.time(); R_, rank = A.rref(); piv = []; r = 0
for c in range(len(cols)):
    if r < rank and int(R_[r, c]) != 0: piv.append(c); r += 1
print(f"K5 system {len(rows)} x {len(cols)}, rank {rank} ({time.time()-t0:.0f}s)", flush=True)
# column norms of w^j * m * F_n over Q (m does not change the norm: the column is the coefficient vector of w^j F_n)
WP = [fmpq_poly([0] * j + [1]) for j in range(5)]
lognorm = {}
for n in NAMES:
    for j in range(5):
        vals = []
        for c in ch[n].values():
            pr = (c * WP[j]) % Rr
            vals += [fmpq(x) for x in pr.coeffs() if fmpq(x) != 0]
        den = 1
        for v in vals: den = den * int(v.q) // math.gcd(den, int(v.q))
        s = sum((int(v.p) * (den // int(v.q))) ** 2 for v in vals)
        lognorm[(n, j)] = 0.5 * math.log10(s)
hb = sum(lognorm[(cols[c][0], j)] for c in piv for j in range(5))
print(f"full chart, weight {W}: Q-rank ~ {5*rank}, Hadamard bound {hb:,.0f} digits; "
      f"calibrated estimate of the max height (x0.046-0.061): {0.046*hb:,.0f} - {0.061*hb:,.0f} digits")
