"""Hadamard bound log10|det(A_B)| <= sum_j log10 ||col_j||_2 for the square pivot block A_B of the canonical solve,
integerised column by column (each column scaled by its common denominator).  Calibrated on the t1 = 0 slice
(D = 2, 3, 4: true heights known) and evaluated for the full chart (weight 24).  Columns: w-expanded (over Q)."""
import sys, os, math, time
sys.path.insert(0, os.path.abspath(".")); sys.path.insert(0, os.path.abspath("step1"))
from lowerc_chart import *
from certlin import build
from flint import nmod_mat, fmpq
def red_p(v, p):
    v = fmpq(v); return int(v.p) % p * pow(int(v.q) % p, p - 2, p) % p
def pivots(cols, cps, rows, ridx, p=1000003):
    A = nmod_mat(len(rows), len(cols), p)
    for c, cp in enumerate(cps):
        for key, v in cp.items(): A[ridx[key], c] = red_p(v, p)
    R_, rank = A.rref(); piv = []; r = 0
    for c in range(len(cols)):
        if r < rank and int(R_[r, c]) != 0: piv.append(c); r += 1
    return piv
def logcolnorm(cp):
    den = 1
    for v in cp.values(): den = den * int(fmpq(v).q) // math.gcd(den, int(fmpq(v).q))
    s = 0
    for v in cp.values():
        n = int(fmpq(v).p) * (den // int(fmpq(v).q)); s += n * n
    return 0.5 * math.log10(s) if s else 0
def bound(gens, degs, nvar, target):
    cols, cps, rows, ridx, rhs = build(gens, degs, target, nvar)
    piv = pivots(cols, cps, rows, ridx)
    return len(piv), sum(logcolnorm(cps[c]) for c in piv)
C7 = load7(); kap = kappa(C7)
B = chart(C7, kap, t1=Z); gB = [B[n] for n in NAMES]
for D, true_h in [(2, 9681), (3, 16274), (4, 18918)]:
    r, hb = bound(gB, [D] * 6, 4, {(0, 0, 0, 0): fmpq_poly([1])})
    print(f"slice t1=0, D={D}: Q-rank {r}, Hadamard bound {hb:,.0f} digits, true max height {true_h:,} (ratio {true_h/hb:.3f})", flush=True)
