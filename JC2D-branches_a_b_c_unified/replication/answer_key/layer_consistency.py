"""
layer_consistency.py -- answer key C2b: which branch-(c) weights impose conditions, checked exactly over K5 at random
rational points (probabilistic identity testing; every step is exact arithmetic).

DO NOT READ OR RUN THIS BEFORE YOU HAVE RECORDED YOUR OWN RESULTS (see ../INDEPENDENT_REPLICATION_GUIDE.md).

Shares no code with the project's lower_c.py / make_cert_c.py. Input: the K5 top-layer point (key "top" of
branches_a_b/lean/certgen/cert.json). The bracket is rebuilt with sympy from the branch-(c) polygons.
At weight d (3, 2, 1, 0, -1) the equations are linear in the new unknowns (P-layer d - 2, Q-layer d - 1) with
coefficients from the top layer only; the lower unknowns already fixed enter the constant terms. The free unknowns
are given random values (b_11_20, b_12_22 at weight 3; b_11_21, b_12_23 at weight 2; a_6_13, a_7_15 at weight 1;
b_10_21 at weight 0), the other new unknowns are solved for, and the script records whether the layer is consistent.
Expected (a condition is a polynomial in the free unknowns that must vanish):
  - weights 3, 2, 1: consistent at every random point, so no condition;
  - weight 0: inconsistent at random b_12_23, consistent when b_12_23 = kappa b_12_22^2 with kappa = 1/(3 b_12_21),
    whatever the other free values: the only weight-0 condition is Omega, a function of (b_12_22, b_12_23) alone;
  - weight -1: inconsistent at random points of {Omega = 0}: weight -1 imposes further conditions.
Run: python3 layer_consistency.py   (about 10 s)
"""
import json, os, random, sys
from fractions import Fraction
import sympy as sp
from flint import fmpq_poly, fmpq

HERE = os.path.dirname(os.path.abspath(__file__))
UNI = os.path.abspath(os.path.join(HERE, "..", ".."))
CERT = os.path.join(UNI, "branches_a_b", "lean", "certgen", "cert.json")
ok = [0, 0]
def check(cond, label, value):
    print(("PASS  " if cond else "FAIL  ") + f"{label}: {value}", flush=True)
    ok[0 if cond else 1] += 1

Rr = fmpq_poly([26, 0, 3, 3, -1, 1])
ZERO, ONE = fmpq_poly([0]), fmpq_poly([1])
def K(c):
    return fmpq_poly([fmpq(Fraction(s).numerator, Fraction(s).denominator) for s in c]) % Rr
def kinv(a):
    g, s, _ = a.xgcd(Rr)
    assert g == 1
    return s % Rr
def kq(r):
    r = Fraction(r)
    return fmpq_poly([fmpq(r.numerator, r.denominator)])

# ---------------------------------------------------------------- branch-(c) bracket, by sympy
def inP(i, j): return 0 <= i <= 8 and j >= 0 and j >= 2 * i - 2 and j <= 8 + i
def inQ(k, l): return 0 <= k <= 12 and 2 * l >= k and l >= 2 * k - 3 and l <= 12 + k
LP = [(i, j) for i in range(9) for j in range(17) if inP(i, j)]
LQ = [(k, l) for k in range(13) for l in range(25) if inQ(k, l)]
assert (len(LP), len(LQ)) == (61, 125)
x, y = sp.symbols("x y")
P = sum(sp.Symbol(f"a_{i}_{j}") * x**i * y**j for i, j in LP)
Q = sum(sp.Symbol(f"b_{k}_{l}") * x**k * y**l for k, l in LQ)
J = sp.Poly(sp.expand(sp.diff(P, x) * sp.diff(Q, y) - sp.diff(P, y) * sp.diff(Q, x)), x, y)
EQ = {}
for (A, B), c in J.terms():
    EQ.setdefault(2 * A - B, []).append(sp.Poly(c, *sorted(c.free_symbols, key=str)))
def layer(v):
    _, i, j = v.split("_")
    return 2 * int(i) - int(j)

cert = json.load(open(CERT))
TOP = {v: K(c) for v, c in cert["top"].items()}
kappa = kinv((3 * TOP["b_12_21"]) % Rr)

def linear_layer(d, known):
    """the weight-d equations as (rows of coefficients of the new unknowns, constants, new unknowns)"""
    new = sorted({str(s) for p in EQ[d] for s in p.gens if str(s) not in known and
                  ((str(s)[0] == "a" and layer(str(s)) == d - 2) or (str(s)[0] == "b" and layer(str(s)) == d - 1))})
    rows, consts = [], []
    for p in EQ[d]:
        row = {v: ZERO for v in new}
        const = ZERO
        for mono, c in zip(p.monoms(), p.coeffs()):
            val = kq(sp.Rational(c))
            lin = None
            for g, e in zip(p.gens, mono):
                for _ in range(e):
                    if str(g) in new:
                        assert lin is None, "not linear in the new unknowns"
                        lin = str(g)
                    else:
                        val = (val * known[str(g)]) % Rr
            if lin is None:
                const = (const + val) % Rr
            else:
                row[lin] = (row[lin] + val) % Rr
        rows.append([row[v] for v in new])
        consts.append(const)
    return rows, consts, new

def rank(M):
    M = [r[:] for r in M]
    rk = 0
    for c in range(len(M[0]) if M else 0):
        piv = next((r for r in range(rk, len(M)) if M[r][c] != 0), None)
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        iv = kinv(M[rk][c])
        for r in range(len(M)):
            if r != rk and M[r][c] != 0:
                f = (M[r][c] * iv) % Rr
                M[r] = [(a - f * b) % Rr for a, b in zip(M[r], M[rk])]
        rk += 1
    return rk

def solve_layer(d, known, free_vals):
    """fix the free new unknowns, solve for the others; returns (consistent, extended known)"""
    rows, consts, new = linear_layer(d, known)
    fixed = dict(free_vals)
    assert set(fixed) <= set(new), (d, set(fixed) - set(new))
    rest = [v for v in new if v not in fixed]
    A = [[r[new.index(v)] for v in rest] for r in rows]
    b = []
    for r, c in zip(rows, consts):
        acc = (-c) % Rr
        for v, val in fixed.items():
            acc = (acc - r[new.index(v)] * val) % Rr
        b.append(acc)
    rA = rank(A)
    assert rA == len(rest), f"weight {d}: the chosen free unknowns are not complementary to the pivots"
    consistent = rank([a + [bb] for a, bb in zip(A, b)]) == rA
    # solve by elimination on the augmented matrix (unique solution when consistent)
    M = [a + [bb] for a, bb in zip(A, b)]
    sol, rk = {}, 0
    pivcols = []
    for c in range(len(rest)):
        piv = next(r for r in range(rk, len(M)) if M[r][c] != 0)
        M[rk], M[piv] = M[piv], M[rk]
        iv = kinv(M[rk][c])
        M[rk] = [(a * iv) % Rr for a in M[rk]]
        for r in range(len(M)):
            if r != rk and M[r][c] != 0:
                f = M[r][c]
                M[r] = [(a - f * bb) % Rr for a, bb in zip(M[r], M[rk])]
        pivcols.append(c)
        rk += 1
    for i, c in enumerate(pivcols):
        sol[rest[c]] = M[i][-1]
    out = dict(known)
    out.update(fixed)
    out.update(sol)
    return consistent, out, len(rows), len(new), rank(rows)

FREE = {3: ["b_11_20", "b_12_22"], 2: ["b_11_21", "b_12_23"], 1: ["a_6_13", "a_7_15"], 0: ["b_10_21"], -1: []}
def run(seed, omega_on):
    rnd = random.Random(seed)
    def rv(): return kq(Fraction(rnd.choice([-1, 1]) * rnd.randint(1, 9), rnd.randint(1, 5)))
    known = dict(TOP)
    result = {}
    for d in (3, 2, 1, 0, -1):
        fv = {v: rv() for v in FREE[d]}
        if d == 2 and omega_on:
            fv["b_12_23"] = (kappa * known["b_12_22"] * known["b_12_22"]) % Rr
        consistent, known, nrows, nnew, rk = solve_layer(d, known, fv)
        result[d] = consistent
    return result

for seed in (1, 2, 3):
    r = run(seed, omega_on=False)
    check(r[3] and r[2] and r[1] and not r[0],
          f"random point {seed}, b_12_23 random: weights 3, 2, 1 consistent; weight 0 inconsistent", r)
for seed in (11, 12, 13):
    r = run(seed, omega_on=True)
    check(r[3] and r[2] and r[1] and r[0] and not r[-1],
          f"random point {seed}, b_12_23 = kappa b_12_22^2: weights 3..0 consistent; weight -1 inconsistent", r)
print(f"LAYER CONSISTENCY CHECKS: {ok[0]} passed, {ok[1]} failed")
sys.exit(1 if ok[1] else 0)
