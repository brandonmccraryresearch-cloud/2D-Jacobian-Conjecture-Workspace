"""Full chart (T2 = 1, S2 = kappa) of lower_c's ideal: weighted Macaulay system for 1 = sum c_i F_i with
wdeg(c_i) <= W - wt(F_i) (weights t 1, s 2, r 3, u 3, q 4).  Size, rank and consistency mod p at a root of R
(rank over K5 = rank at a good root, generically)."""
import sys, os, itertools, time
sys.path.insert(0, os.path.abspath("step1"))
from lowerc_chart import *
from flint import nmod_mat
from fractions import Fraction as Fr
C7 = load7(); kap = kappa(C7); ch = chart(C7, kap)
WT = (1, 2, 3, 3, 4); WTF = {"Psi": 5, "Phi1": 6, "Phi2": 6, "Theta1": 7, "Theta2": 7, "Theta3": 7}
def monos_upto(W):
    out = []
    for t in range(W + 1):
        for s in range((W - t) // 2 + 1):
            for r in range((W - t - 2 * s) // 3 + 1):
                for u in range((W - t - 2 * s - 3 * r) // 3 + 1):
                    for q in range((W - t - 2 * s - 3 * r - 3 * u) // 4 + 1):
                        out.append((t, s, r, u, q))
    return out
def red(a, p, w):
    t = 0
    for k, c in enumerate(a.coeffs()):
        f = Fr(str(c)); t = (t + f.numerator * pow(f.denominator, -1, p) * pow(w, k, p)) % p
    return t
p, w = 1000003, 806739
G = {n: {m: red(c, p, w) for m, c in ch[n].items()} for n in NAMES}
for W in [int(x) for x in sys.argv[1:]]:
    t0 = time.time()
    cols = [(n, m) for n in NAMES for m in monos_upto(W - WTF[n])]
    rowset = {}
    for n, m in cols:
        for mm in G[n]: rowset.setdefault(tuple(a + b for a, b in zip(m, mm)), None)
    rowset.setdefault((0, 0, 0, 0, 0), None)
    rows = list(rowset); ridx = {r: i for i, r in enumerate(rows)}
    A = nmod_mat(len(rows), len(cols) + 1, p)
    for j, (n, m) in enumerate(cols):
        for mm, c in G[n].items():
            if c: A[ridx[tuple(a + b for a, b in zip(m, mm))], j] = c
    A0 = nmod_mat(len(rows), len(cols), p)
    for j, (n, m) in enumerate(cols):
        for mm, c in G[n].items():
            if c: A0[ridx[tuple(a + b for a, b in zip(m, mm))], j] = c
    A[ridx[(0, 0, 0, 0, 0)], len(cols)] = 1
    r0, r1 = A0.rank(), A.rank()
    print(f"W={W}: K5 system {len(rows)} x {len(cols)}, rank {r0}, augmented {r1} -> "
          f"{'consistent' if r0 == r1 else 'inconsistent'}  ({time.time()-t0:.0f}s)", flush=True)
