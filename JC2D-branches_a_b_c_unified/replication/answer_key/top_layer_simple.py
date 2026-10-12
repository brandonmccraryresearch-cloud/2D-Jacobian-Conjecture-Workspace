"""
top_layer_simple.py -- answer key R3a/R3b: the top-layer solutions are simple (multiplicity one), exactly over K5.

DO NOT READ OR RUN THIS BEFORE YOU HAVE RECORDED YOUR OWN RESULTS (see ../INDEPENDENT_REPLICATION_GUIDE.md).

Input: the K5 top-layer point (key "top" of branches_a_b/lean/certgen/cert.json), alpha_i = a_{i+1,2i},
beta_j = b_{j+2,2j+1}. It is moved by the torus u -> u/alpha_1 into the chart alpha_0 = beta_0 = alpha_1 = 1 of R3b.

Chart R3b: unknowns alpha_2..alpha_7; beta_1..beta_10 are eliminated by the recursion of the equations k = 1..10;
the equations k = 11..16 are six polynomials C_11..C_16 in alpha_2..alpha_7. The script checks, exactly over K5:
  1. the moved point solves C_11..C_16, and its beta's are those of the recursion;
  2. det(dC_k/dalpha_j) at the point is a nonzero element of K5, so all five Galois conjugates are simple solutions.
Consequence for R3a: the chart alpha_7 = 1 is reached from the chart alpha_1 = 1 by u -> s u with s^7 = 1/alpha_7,
an etale (mu_7) change of slice in characteristic 0, so all 35 solutions of R3a are simple as well (all of them have
alpha_1 != 0, by the classification).
Run: python3 top_layer_simple.py   (a few seconds)
"""
import json, os, sys
from fractions import Fraction
import sympy as sp
from flint import fmpq_poly, fmpq

HERE = os.path.dirname(os.path.abspath(__file__))
UNI = os.path.abspath(os.path.join(HERE, "..", ".."))
CERT = os.path.join(UNI, "branches_a_b", "lean", "certgen", "cert.json")
ok = [0, 0]
def check(cond, label, value):
    print(("PASS  " if cond else "FAIL  ") + f"{label}: {value}")
    ok[0 if cond else 1] += 1

Rr = fmpq_poly([26, 0, 3, 3, -1, 1])
def K(c):
    return fmpq_poly([fmpq(Fraction(s).numerator, Fraction(s).denominator) for s in c]) % Rr
def kinv(a):
    g, s, _ = a.xgcd(Rr)
    assert g == 1
    return s % Rr
def kq(r):
    r = sp.Rational(r)
    return fmpq_poly([fmpq(int(r.p), int(r.q))])

top = {v: K(c) for v, c in json.load(open(CERT))["top"].items()}
alpha = [top[f"a_{i + 1}_{2 * i}"] for i in range(8)]          # alpha_0..alpha_7
beta = [top[f"b_{j + 2}_{2 * j + 1}"] for j in range(11)]      # beta_0..beta_10
assert alpha[0] == 1 and beta[0] == 1
s_inv = kinv(alpha[1])                                          # u -> u / alpha_1
pw = [fmpq_poly([1])]
for _ in range(10):
    pw.append((pw[-1] * s_inv) % Rr)
alphaB = [(alpha[i] * pw[i]) % Rr for i in range(8)]
betaB = [(beta[j] * pw[j]) % Rr for j in range(11)]
check(alphaB[0] == 1 and alphaB[1] == 1 and betaB[0] == 1, "moved point is in the chart alpha_0 = alpha_1 = beta_0 = 1", True)

# symbolic system of the chart alpha_0 = beta_0 = alpha_1 = 1
A = [sp.Integer(1), sp.Integer(1)] + list(sp.symbols("al2:8"))
B = [sp.Integer(1)]
for k in range(1, 11):
    f = sum((1 + 2 * (k - i) - 3 * i) * A[i] * B[k - i] for i in range(1, min(k, 7) + 1))
    B.append(sp.expand(-f / (1 + 2 * k)))
C = [sp.expand(sum((1 + 2 * (k - i) - 3 * i) * A[i] * B[k - i] for i in range(0, 8) if 0 <= k - i <= 10))
     for k in range(11, 17)]
X = A[2:]
def ev(expr):
    """evaluate a polynomial in al2..al7 with rational coefficients at the moved point, in K5"""
    p = sp.Poly(expr, *X)
    acc = fmpq_poly([0])
    for mono, c in zip(p.monoms(), p.coeffs()):
        t = kq(c)
        for xi, e in zip(range(2, 8), mono):
            for _ in range(e):
                t = (t * alphaB[xi]) % Rr
        acc = (acc + t) % Rr
    return acc
check(all(ev(c) == 0 for c in C), "the moved point solves C_11..C_16 exactly over K5", True)
check(all(ev(B[j]) == betaB[j] for j in range(1, 11)), "its beta_1..beta_10 are those of the recursion", True)
Jm = [[ev(sp.diff(c, xv)) for xv in X] for c in C]
def det(M):
    M = [r[:] for r in M]
    n = len(M)
    d = fmpq_poly([1])
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c] != 0), None)
        if piv is None:
            return fmpq_poly([0])
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            d = -d
        d = (d * M[c][c]) % Rr
        iv = kinv(M[c][c])
        for r in range(c + 1, n):
            if M[r][c] != 0:
                f = (M[r][c] * iv) % Rr
                M[r] = [(a - f * b) % Rr for a, b in zip(M[r], M[c])]
    return d
D = det(Jm)
check(D != 0, "det of the 6 x 6 Jacobian (dC_k/dalpha_j) at the point is a nonzero element of K5", D != 0)
print("  a nonzero element of the field K5 stays nonzero under all five embeddings, so all five conjugate points are simple")
print(f"TOP LAYER SIMPLE CHECKS: {ok[0]} passed, {ok[1]} failed")
sys.exit(1 if ok[1] else 0)
