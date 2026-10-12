"""
macaulay_rank.py -- answer key C3: the weighted Macaulay matrices M_W (W = 22, 23, 24) of the six branch-(c) chart
generators, their sizes and nonzero counts, and their ranks modulo two primes, with the planted-zero control.

DO NOT READ OR RUN THIS BEFORE YOU HAVE RECORDED YOUR OWN RESULTS (see ../INDEPENDENT_REPLICATION_GUIDE.md).

Written from the guide's description of target C3 alone. It shares no code with branch_c/rank_lemma_check/ or with
key_checks.py. Input: branch_c/bundle_v3_1/jacobian_lean/certgen_c/conds_c.json (route A of the guide).

Construction, as in the guide:
  - kappa = -o2/(2 o1) from the three coefficients of Omega;
  - F_n = condition n at b_12_22 = 1, b_12_23 = kappa, computed exactly in K5 = Q[w]/(R), a polynomial in
    (t, s, r, u, q) = (b_11_20, b_11_21, a_6_13, a_7_15, b_10_21) with weights (1, 2, 3, 3, 4);
  - columns: pairs (n, m), m a monomial with wdeg(m) <= W - wdeg(F_n); rows: the monomials of the K5 supports of
    the products m * F_n, together with 1; entries: the coefficients;
  - each K5 coefficient is mapped to F_p by w -> w0, after checking that its denominators are prime to p and that
    no coefficient of any F_n vanishes mod p (so the supports mod p are the K5 supports).
Ranks are computed with FLINT's nmod_mat (exact arithmetic mod p).

Last line: "MACAULAY CHECKS: n passed, m failed". Runtime a few minutes, memory below 1 GB.
Run: python3 macaulay_rank.py
"""
import json, os, sys, random, time, resource
from fractions import Fraction
from flint import fmpq_poly, fmpq, nmod_mat

HERE = os.path.dirname(os.path.abspath(__file__))
UNI = os.path.abspath(os.path.join(HERE, "..", ".."))
CONDS = os.path.join(UNI, "branch_c", "bundle_v3_1", "jacobian_lean", "certgen_c", "conds_c.json")
ok = [0, 0]
def check(cond, label, value):
    print(("PASS  " if cond else "FAIL  ") + f"{label}: {value}", flush=True)
    ok[0 if cond else 1] += 1

# ---------------------------------------------------------------- K5 = Q[w]/(R)
Rr = fmpq_poly([26, 0, 3, 3, -1, 1])                    # R = w^5 - w^4 + 3 w^3 + 3 w^2 + 26
def K(c):
    return fmpq_poly([fmpq(Fraction(s).numerator, Fraction(s).denominator) for s in c]) % Rr
def kinv(a):
    g, s, _ = a.xgcd(Rr)
    assert g == 1
    return s % Rr
def to_p(a, p, w0):
    """image of a in F_p under w -> w0; None if a denominator is divisible by p"""
    acc = 0
    for i in range(a.degree() + 1):
        q = Fraction(int(a[i].p), int(a[i].q))
        if q.denominator % p == 0:
            return None
        acc = (acc + q.numerator * pow(q.denominator, -1, p) * pow(w0, i, p)) % p
    return acc

# ---------------------------------------------------------------- the chart generators over K5
conds = json.load(open(CONDS))
def terms_of(name):
    out = []
    for mono, coef in conds[name]:
        ex = {}
        for v, e in mono:
            ex[v] = ex.get(v, 0) + e
        out.append((ex, K(coef)))
    return out
omega = {tuple(sorted(ex.items())): c for ex, c in terms_of("Omega")}
o1 = omega[(("b_12_23", 2),)]
o2 = omega[(("b_12_22", 2), ("b_12_23", 1))]
o3 = omega[(("b_12_22", 4),)]
assert len(omega) == 3 and (o2 * o2) % Rr == (4 * o1 * o3) % Rr
kappa = (-o2 * kinv((2 * o1) % Rr)) % Rr

CHART = ("b_11_20", "b_11_21", "a_6_13", "a_7_15", "b_10_21")    # t, s, r, u, q
WTS = (1, 2, 3, 3, 4)
NAMES = ("Psi", "Phi1", "Phi2", "Theta1", "Theta2", "Theta3")
def wdeg(m):
    return sum(a * w for a, w in zip(m, WTS))
F = {}
for n in NAMES:
    acc = {}
    for ex, c in terms_of(n):
        ex = dict(ex)
        for _ in range(ex.pop("b_12_23", 0)):
            c = (c * kappa) % Rr
        ex.pop("b_12_22", None)                          # b_12_22 = 1
        assert set(ex) <= set(CHART), ex
        m = tuple(ex.get(v, 0) for v in CHART)
        acc[m] = (acc.get(m, fmpq_poly([0])) + c) % Rr
    F[n] = {m: c for m, c in acc.items() if c != 0}
deg = {n: max(wdeg(m) for m in F[n]) for n in NAMES}
check([len(F[n]) for n in NAMES] == [22, 35, 35, 52, 52, 52] and [deg[n] for n in NAMES] == [5, 6, 6, 7, 7, 7],
      "F_n over K5: nonzero terms, weighted degrees", ([len(F[n]) for n in NAMES], [deg[n] for n in NAMES]))

def monomials(D):
    """all exponent vectors (a, b, c, d, e) with a + 2b + 3c + 3d + 4e <= D"""
    out = []
    for e in range(D // 4 + 1):
        for d in range((D - 4 * e) // 3 + 1):
            for c in range((D - 4 * e - 3 * d) // 3 + 1):
                for b in range((D - 4 * e - 3 * d - 3 * c) // 2 + 1):
                    for a in range(D - 4 * e - 3 * d - 3 * c - 2 * b + 1):
                        out.append((a, b, c, d, e))
    return out

def macaulay(W, Fp, p, extra_col=False):
    """M_W mod p (optionally with the extra column e_1 at the row of the monomial 1);
    returns (matrix, rows, number of columns per generator, nnz)"""
    cols = [(n, m) for n in NAMES for m in monomials(W - deg[n])]
    rows = sorted({tuple(x + y for x, y in zip(m, mu)) for n, m in cols for mu in F[n]} | {(0, 0, 0, 0, 0)})
    idx = {mu: i for i, mu in enumerate(rows)}
    M = nmod_mat(len(rows), len(cols) + (1 if extra_col else 0), p)
    nnz = 0
    for j, (n, m) in enumerate(cols):
        for mu, c in Fp[n].items():
            if c:
                M[idx[tuple(x + y for x, y in zip(m, mu))], j] = c
                nnz += 1
    if extra_col:
        M[idx[(0, 0, 0, 0, 0)], len(cols)] = 1
    per_gen = [sum(1 for n_, _ in cols if n_ == n) for n in NAMES]
    return M, rows, cols, per_gen, nnz

WANT = {22: (2281, 3934, 2277, 2278), 23: (2708, 4904, 2707, 2708), 24: (3199, 6054, 3199, 3199)}
t0 = time.time()
for p, w0 in ((32003, 11147), (1000003, 806739)):
    check((w0**5 - w0**4 + 3 * w0**3 + 3 * w0**2 + 26) % p == 0, f"R(w0) = 0 mod {p} (w0 = {w0})", True)
    Fp = {}
    good = True
    for n in NAMES:
        Fp[n] = {}
        for m, c in F[n].items():
            v = to_p(c, p, w0)
            good &= v is not None and v != 0
            Fp[n][m] = v
    check(good, f"mod {p}: every coefficient of every F_n is p-integral and nonzero mod p", good)
    if not good:
        continue
    for W in (22, 23, 24):
        M, rows, cols, per_gen, nnz = macaulay(W, Fp, p)
        rk = M.rank()
        del M
        Ma, _, _, _, _ = macaulay(W, Fp, p, extra_col=True)
        rka = Ma.rank()
        del Ma
        got = (len(rows), len(cols), rk, rka)
        check(got == WANT[W], f"mod {p}, W = {W}: rows, columns, rank, rank of [M | e_1]", got)
        if W == 24:
            check(nnz == 239154, f"mod {p}, W = 24: nonzero entries", nnz)
            check(per_gen == [1308, 1071, 1071, 868, 868, 868], f"mod {p}, W = 24: columns per generator", per_gen)
    # planted-zero control: F_n - F_n(x) has the common zero x, so M_24 cannot have full row rank
    rnd = random.Random(20261007 + p)
    x = [rnd.randrange(p) for _ in range(5)]
    Fq = {}
    for n in NAMES:
        val = sum(c * pow(x[0], m[0], p) * pow(x[1], m[1], p) * pow(x[2], m[2], p) * pow(x[3], m[3], p)
                  * pow(x[4], m[4], p) for m, c in Fp[n].items()) % p
        Fq[n] = dict(Fp[n])
        Fq[n][(0, 0, 0, 0, 0)] = (Fq[n].get((0, 0, 0, 0, 0), 0) - val) % p
    M, rows, cols, _, _ = macaulay(24, Fq, p)
    rk = M.rank()
    del M
    check(rk <= 3198, f"mod {p}, planted common zero x = {x}: rank of M_24 drops below 3199", rk)
    print(f"  [{time.time() - t0:.0f} s elapsed]", flush=True)
print(f"peak memory: {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024} MB")
print(f"MACAULAY CHECKS: {ok[0]} passed, {ok[1]} failed")
sys.exit(1 if ok[1] else 0)
