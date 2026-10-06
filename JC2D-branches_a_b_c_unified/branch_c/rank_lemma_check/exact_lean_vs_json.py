"""exact_lean_vs_json.py -- premise H6 of README.md, exactly over K5 = Q[w]/(R).

The rank lemma is computed from certgen_c/conds_c.json (via step3b_rank_lift.py and step1/lowerc_chart.py).
ChartEmptyC_T1ne0 quantifies over the Lean definitions cond_* of Jacobian/BranchC/CondsC.lean.  This script parses
CondsC.lean from its own text (no generator, no JSON), expands all 110 definitions exactly as integer polynomials in
(w, b_11_20, b_12_22, b_11_21, b_12_23, a_6_13, a_7_15, b_10_21), reduces the w-part modulo R, and checks for each of
the twelve conditions:
  * the same support as conds_c.json, and
  * proportionality: cond_n = lambda_n * conds_c.json[n] for a single lambda_n in K5 (cross-multiplication of all
    coefficients); lambda_n is reported (it is a positive integer for all twelve).
It also checks, on the Lean side, the chart identity  cond_Omega = o1 (S2 - kappa T2^2)^2  with o1 != 0, where kappa
is computed from conds_c.json by lowerc_chart.kappa, and reports whether o1 is rational.
Controls (each must be rejected): one numeral of cond_Psi changed by +1; kappa replaced by kappa + 1.
usage: python3 exact_lean_vs_json.py CondsC.lean CHART_CERTIFICATES_DIR      (needs python-flint)
"""
import sys, os, re, time
from flint import fmpq_poly

LEAN, CH = sys.argv[1], sys.argv[2]
sys.set_int_max_str_digits(0)
sys.path.insert(0, CH)
sys.path.insert(0, os.path.join(CH, "step1"))
import lowerc_chart as LC                       # read-only; run with PYTHONDONTWRITEBYTECODE=1

Rr = LC.Rr
VARS = ["w", "b_11_20", "b_12_22", "b_11_21", "b_12_23", "a_6_13", "a_7_15", "b_10_21"]
assert VARS[1:] == LC.V7


class P:
    """polynomial with integer coefficients in the eight variables: {exponent tuple: int}"""
    __slots__ = ("d",)

    def __init__(self, d):
        self.d = d

    @staticmethod
    def c(n):
        return P({(0,) * 8: n} if n else {})

    def __add__(a, b):
        b = b if isinstance(b, P) else P.c(b)
        d = dict(a.d)
        for k, v in b.d.items():
            x = d.get(k, 0) + v
            if x:
                d[k] = x
            else:
                d.pop(k, None)
        return P(d)

    __radd__ = __add__

    def __mul__(a, b):
        b = b if isinstance(b, P) else P.c(b)
        d = {}
        for k1, v1 in a.d.items():
            for k2, v2 in b.d.items():
                k = tuple(x + y for x, y in zip(k1, k2))
                x = d.get(k, 0) + v1 * v2
                if x:
                    d[k] = x
                else:
                    d.pop(k, None)
        return P(d)

    __rmul__ = __mul__

    def __neg__(a):
        return P({k: -v for k, v in a.d.items()})

    def __pow__(a, e):
        r = P.c(1)
        for _ in range(e):
            r = r * a
        return r


ARGS = " ".join(VARS)
src = open(LEAN).read()
defs = re.findall(r"noncomputable def (cond_\w+) \(" + ARGS + r" : L\) : L :=\n(.*?)\n\n", src, re.S)
assert len(defs) == src.count("noncomputable def"), "a definition of CondsC.lean was not parsed"


def translate(body):
    e = re.sub(r"\((-?\d+) : L\)", r"(\1)", body.strip())
    e = re.sub(r"(cond_\w+) " + ARGS, r"V['\1']", e).replace("^", "**")
    assert not re.search(r"[^\w\s()+\-*\[\]']", e), "unexpected syntax in CondsC.lean"
    return e


EXPR = {name: translate(body) for name, body in defs}


def expand(expr):
    env = {v: P({tuple(1 if j == i else 0 for j in range(8)): 1}) for i, v in enumerate(VARS)}
    V = {}
    env["V"] = V
    for name, _ in defs:
        V[name] = eval(compile(expr[name], name, "eval"), {}, env)
    return V


def to_k5(Pl):
    """{7-variable exponent: K5 coefficient}, the w-part reduced modulo R"""
    out = {}
    for k, v in Pl.d.items():
        out[k[1:]] = out.get(k[1:], fmpq_poly([0])) + fmpq_poly([0] * k[0] + [v])
    return {k: x % Rr for k, x in out.items() if x % Rr != 0}


def compare(Lk, Jk):
    same_supp = set(Lk) == set(Jk)
    if not same_supp:
        return False, False, None
    m0 = min(Jk)
    prop = all((Lk[m] * Jk[m0] - Lk[m0] * Jk[m]) % Rr == 0 for m in Jk)
    return same_supp, prop, (Lk[m0] * LC.kinv(Jk[m0])) % Rr


def omega_identity(Om, kap):
    keys = {(0, 0, 0, 2, 0, 0, 0), (0, 2, 0, 1, 0, 0, 0), (0, 4, 0, 0, 0, 0, 0)}
    o1 = Om.get((0, 0, 0, 2, 0, 0, 0))
    ok = (set(Om) == keys and o1 is not None and o1 != 0
          and (Om[(0, 2, 0, 1, 0, 0, 0)] + 2 * o1 * kap) % Rr == 0
          and (Om[(0, 4, 0, 0, 0, 0, 0)] - o1 * kap * kap) % Rr == 0)
    return ok, o1


t0 = time.time()
V = expand(EXPR)
print(f"{len(defs)} Lean definitions parsed from {os.path.basename(LEAN)} ({len(src) / 1e6:.2f} MB) and expanded "
      f"exactly in {time.time() - t0:.1f} s")
C7 = LC.load7()
tops = [n for n, _ in defs if not re.search(r"_c\d+$", n)]
print(f"{len(tops)} conditions: {', '.join(tops)}")
allok = len(tops) == 12
for n in tops:
    Lk, Jk = to_k5(V[n]), C7.get(n[len("cond_"):])
    if Jk is None:
        print(f"  {n}: missing from conds_c.json")
        allok = False
        continue
    same, prop, lam = compare(Lk, Jk)
    if lam is not None and lam.degree() == 0:
        q = lam.coeffs()[0]
        lam_s = f"{'positive integer' if q.q == 1 and q.p > 0 else 'rational'} {q}"
    else:
        lam_s = "not a nonzero rational"
    print(f"  {n:20s} Lean terms {len(V[n].d):4d} -> K5-monomials {len(Lk):3d}; json {len(Jk):3d}; "
          f"same support {same}; proportional {prop}; lambda {lam_s}")
    allok &= same and prop
kap = LC.kappa(C7)
ident, o1 = omega_identity(to_k5(V["cond_Omega"]), kap)
print(f"Lean cond_Omega = o1 (S2 - kappa T2^2)^2 exactly, o1 != 0: {ident}; o1 rational: {o1.degree() == 0}")
allok &= ident
# controls
bad = dict(EXPR)
first = re.search(r"\((-?\d+)\)", bad["cond_Psi_c0"])
bad["cond_Psi_c0"] = bad["cond_Psi_c0"][:first.start()] + f"({int(first.group(1)) + 1})" + bad["cond_Psi_c0"][first.end():]
_, prop_bad, _ = compare(to_k5(expand(bad)["cond_Psi"]), C7["Psi"])
ident_bad, _ = omega_identity(to_k5(V["cond_Omega"]), (kap + 1) % Rr)
print(f"control: one numeral of cond_Psi + 1 -> proportional {prop_bad} (must be False)")
print(f"control: kappa + 1 -> Omega identity {ident_bad} (must be False)")
ctrl_ok = (not prop_bad) and (not ident_bad)
print("ALL PROPORTIONAL; CONTROLS REJECTED" if allok and ctrl_ok else "MISMATCH OR CONTROL NOT REJECTED")
sys.exit(0 if allok and ctrl_ok else 1)
