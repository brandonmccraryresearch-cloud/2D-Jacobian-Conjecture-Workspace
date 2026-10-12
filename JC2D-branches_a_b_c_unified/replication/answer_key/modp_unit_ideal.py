"""
modp_unit_ideal.py -- answer key C2c: for every prime 101 <= p < 700 and every root w0 of R mod p, do the six
branch-(c) chart generators F_n (b_12_22 = 1, b_12_23 = kappa) generate the unit ideal in F_p[t, s, r, u, q]?

DO NOT READ OR RUN THIS BEFORE YOU HAVE RECORDED YOUR OWN RESULTS (see ../INDEPENDENT_REPLICATION_GUIDE.md).

Evidence only: a unit ideal mod p excludes only the common zeros that are integral at the prime above p.
The F_n are built exactly over K5 from branch_c/bundle_v3_1/jacobian_lean/certgen_c/conds_c.json, as in
macaulay_rank.py (no code shared with the project's lower_c.py). A pair (p, w0) is "bad" when some coefficient of
some F_n has a denominator divisible by p. One Singular run decides all pairs.
Needs python-flint, sympy and Singular on PATH (or $SINGULAR). Runtime well under a minute.
Run: python3 modp_unit_ideal.py
"""
import json, os, shutil, subprocess, sys, tempfile
from fractions import Fraction
from flint import fmpq_poly, fmpq
import sympy

HERE = os.path.dirname(os.path.abspath(__file__))
UNI = os.path.abspath(os.path.join(HERE, "..", ".."))
CONDS = os.path.join(UNI, "branch_c", "bundle_v3_1", "jacobian_lean", "certgen_c", "conds_c.json")
SINGULAR = os.environ.get("SINGULAR") or shutil.which("Singular")
if not SINGULAR:
    sys.exit("Singular not found: put it on PATH or set SINGULAR")

Rr = fmpq_poly([26, 0, 3, 3, -1, 1])
def K(c):
    return fmpq_poly([fmpq(Fraction(s).numerator, Fraction(s).denominator) for s in c]) % Rr
def kinv(a):
    g, s, _ = a.xgcd(Rr)
    assert g == 1
    return s % Rr
def to_p(a, p, w0):
    acc = 0
    for i in range(a.degree() + 1):
        q = Fraction(int(a[i].p), int(a[i].q))
        if q.denominator % p == 0:
            return None
        acc = (acc + q.numerator * pow(q.denominator, -1, p) * pow(w0, i, p)) % p
    return acc

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
kappa = (-omega[(("b_12_22", 2), ("b_12_23", 1))] * kinv((2 * omega[(("b_12_23", 2),)]) % Rr)) % Rr
CHART = ("b_11_20", "b_11_21", "a_6_13", "a_7_15", "b_10_21")
VARS = ("t", "s", "r", "u", "q")
NAMES = ("Psi", "Phi1", "Phi2", "Theta1", "Theta2", "Theta3")
F = {}
for n in NAMES:
    acc = {}
    for ex, c in terms_of(n):
        ex = dict(ex)
        for _ in range(ex.pop("b_12_23", 0)):
            c = (c * kappa) % Rr
        ex.pop("b_12_22", None)
        m = tuple(ex.get(v, 0) for v in CHART)
        acc[m] = (acc.get(m, fmpq_poly([0])) + c) % Rr
    F[n] = {m: c for m, c in acc.items() if c != 0}

pairs, script, bad = [], [], []
for p in sympy.primerange(101, 700):
    for w0 in range(p):
        if (w0**5 - w0**4 + 3 * w0**3 + 3 * w0**2 + 26) % p:
            continue
        polys, ok = [], True
        for n in NAMES:
            terms = []
            for m, c in F[n].items():
                v = to_p(c, p, w0)
                if v is None:
                    ok = False
                    break
                if v:
                    terms.append(str(v) + "".join(f"*{x}^{e}" for x, e in zip(VARS, m) if e))
            if not ok:
                break
            polys.append("+".join(terms) if terms else "0")
        if not ok:
            bad.append((p, w0))
            continue
        pairs.append((p, w0))
        script.append(f"ring r{len(pairs)} = {p},({','.join(VARS)}),dp; ideal I = {','.join(polys)};\n"
                      f"print(\"{p} {w0} \" + string(reduce(1, std(I)) == 0)); kill r{len(pairs)};")
with tempfile.NamedTemporaryFile("w", suffix=".sing", delete=False) as fh:
    fh.write("\n".join(script) + "\nquit;\n")
    path = fh.name
out = subprocess.run([SINGULAR, "-q", path], capture_output=True, text=True, stdin=subprocess.DEVNULL, timeout=900).stdout
os.unlink(path)
res = {}
for line in out.split("\n"):
    f = line.split()
    if len(f) == 3 and f[0].isdigit():
        res[(int(f[0]), int(f[1]))] = f[2] == "1"
assert set(res) == set(pairs), "Singular did not report every pair"
unit = [pw for pw in pairs if res[pw]]
nonunit = [pw for pw in pairs if not res[pw]]
print(f"primes 101 <= p < 700: {len(pairs) + len(bad)} pairs (p, w0) with R(w0) = 0 mod p")
print(f"bad pairs (a denominator divisible by p): {len(bad)}: {bad}")
print(f"good pairs: {len(pairs)}; the six chart generators give the unit ideal at {len(unit)} of them")
print(f"good pairs without the unit ideal: {nonunit}")
print(f"excluding p = 101 (the range of the project's lower_c.py): unit ideal at "
      f"{sum(1 for p, _ in unit if p > 101)} of {sum(1 for p, _ in pairs + bad if p > 101)} pairs")
sys.exit(0 if not nonunit else 1)
