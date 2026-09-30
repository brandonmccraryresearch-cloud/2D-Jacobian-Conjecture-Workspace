"""
gen_t1zero_c.py -- exact integer certificates for the chart statement on the stratum b_{11,20} = 0:
  w root of R, b_{11,20} = 0, b_{12,22} = 1, Omega = Psi = Phi1 = Phi2 = Theta1..3 = 0  ->  False.
Imported by gen_t1zero_lean.py, which writes Jacobian/BranchC/T1Zero/*.lean (kernel-checked there).

Steps (facts over Z[w, T1, T2, S1, S2, R1, R2, Q]; each step is an identity target = sum m_i * fact_i):
  A1  e_sq  = D_O * No1 * X^2          from ek_Omega, T2 - 1, R(w)     (Omega = o1 (S2 - kappa T2^2)^2;  X = Dk S2 - Nk)
  A2  c * D_O * X^2                    from e_sq, R(w)                  (Bezout a*No1 + b*R = c: o1(w) != 0)
      -> X^2 = 0 (cancel_int) -> X = 0 (pow_eq_zero_iff)
  B1  f_i = Dk^d_i * ek_i|slice        from ek_i, T1, T2 - 1, X, R(w)   (the six conditions on the slice)
  B2  p_i = nu_i * f_i mod R           from f_i, R(w)                   (nu_i: the step-1 certificate certB_lowerc.json)
  B3  DD = sum_i p_i + A R             -> (DD : L) = 0, impossible in characteristic 0.
All identities are exact integer polynomial identities, checked here before emission.
"""
import json, os, sys, io, contextlib, math
sys.set_int_max_str_digits(0)
from fractions import Fraction
from math import comb
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
with contextlib.redirect_stdout(io.StringIO()):
    import make_cert_c as mc
from flint import fmpq_poly, fmpq
RC = [26, 0, 3, 3, -1, 1]
# the step-1 slice certificate (chart_certificates/step1/certB_lowerc.json, md5 772e4307...); CERTB overrides
CERT = os.environ.get("CERTB", os.path.join(HERE, "..", "chart_certificates", "step1", "certB_lowerc.json"))
V = ["w", "b_11_20", "b_12_22", "b_11_21", "b_12_23", "a_6_13", "a_7_15", "b_10_21"]      # = ALLV[:8] of gen_refl_c
IDX = {v: i for i, v in enumerate(V)}
T1, T2, S1, S2, R1, R2, Q = V[1:]
# ------------------------------------------------ integer polynomials {(mono, wpow): int}
def iadd(A, B, s=1):
    out = dict(A)
    for k, v in B.items():
        x = out.get(k, 0) + s * v
        if x: out[k] = x
        elif k in out: del out[k]
    return out
def iscale(A, c): return {k: v * c for k, v in A.items() if v * c} if c else {}
def imul(A, B):
    out = {}
    for (m1, i1), a in A.items():
        for (m2, i2), b in B.items():
            k = (mc.mono_mul(m1, m2), i1 + i2); out[k] = out.get(k, 0) + a * b
    return {k: v for k, v in out.items() if v}
def by_mono(T):
    d = {}
    for (m, i), v in T.items(): d.setdefault(m, {})[i] = v
    return d
def modR(T):
    out = {}
    for m, d in by_mono(T).items():
        a = [d.get(i, 0) for i in range(max(d) + 1)]
        for k in range(len(a) - 1, 4, -1):
            t = a[k]
            if t:
                for j in range(6): a[k - 5 + j] -= t * RC[j]
        for i in range(min(5, len(a))):
            if a[i]: out[(m, i)] = a[i]
    return out
def divR(T):
    Q_ = {}
    for m, d in by_mono(T).items():
        deg = max(d); a = [d.get(i, 0) for i in range(deg + 1)]
        for k in range(deg, 4, -1):
            t = a[k]
            if t:
                Q_[(m, k - 5)] = t
                for j in range(6): a[k - 5 + j] -= t * RC[j]
        assert all(x == 0 for x in a[:5]), "not divisible by R"
    return Q_
def lcm(a, b): return a * b // math.gcd(a, b)
def to_int(P):
    D = 1
    for c in P.values():
        for i in range(5):
            if c[i] != 0: D = lcm(D, int(c[i].q))
    N = {}
    for m, c in P.items():
        for i in range(5):
            if c[i] != 0:
                v = Fraction(int(c[i].p), int(c[i].q)) * D; assert v.denominator == 1; N[(m, i)] = int(v)
    return D, N
def const(c): return {((), 0): c} if c else {}
def var(x): return {(((x, 1),), 0): 1}
def wpoly(N): return {((), i): c for (m, i), c in N.items()}          # constant-in-vars integer poly in w
eR = {((), i): c for i, c in enumerate(RC) if c}
def expo(m, x): return dict(m).get(x, 0)
def drop(m, x): return tuple((v, e) for v, e in m if v != x)
def with_(m, x, e):
    d = dict(m); d.pop(x, None)
    if e: d[x] = e
    return tuple(sorted(d.items()))
# ------------------------------------------------ conditions (as in gen_refl_c: minimal integer scale)
lc = json.load(open(os.path.join(HERE, "conds_c.json")))
def cond(n): return {tuple(sorted((v, e) for v, e in m)): mc.Kc(cs) for m, cs in lc[n]}
NAMES = ["Psi", "Phi1", "Phi2", "Theta1", "Theta2", "Theta3"]
EK = {n: to_int(cond(n)) for n in ["Omega"] + NAMES}         # (D_n, N_n): ek_n = N_n = D_n * cond_n
# Omega = o1 S2^2 + o2 T2^2 S2 + o3 T2^4 ; kappa = -o2/(2 o1)
Om = cond("Omega")
o1, o2, o3 = Om[((S2, 2),)], Om[tuple(sorted(((T2, 2), (S2, 1))))], Om[((T2, 4),)]
Rr = fmpq_poly(RC)
def kinv(a):
    g, s, _ = a.xgcd(Rr); assert g == 1; return s % Rr
assert (o2 * o2 - 4 * o1 * o3) % Rr == 0
kap = (-o2 * kinv(2 * o1)) % Rr
Dk, Nk = to_int({(): kap}); Nk = wpoly(Nk)
Do1, No1 = to_int({(): o1}); No1 = wpoly(No1)
X = iadd(iscale(var(S2), Dk), Nk, -1)                          # X = Dk S2 - Nk(w)
facts = {"eR": eR, "eT1": var(T1), "eT2": iadd(var(T2), const(1), -1), "eX": X}
for n in ["Omega"] + NAMES: facts[f"ek_{n}"] = EK[n][1]
steps = []                                                    # (thm name, target name or Expr-literal, cert list, new fact?)
def check(target_poly, cl):
    S = dict(target_poly)
    for m, f in cl: S = iadd(S, imul(m, facts[f]), -1)
    assert S == {}, "certificate fails"
# ---------- substitution machinery: P -> (P restricted, multipliers)
def split_T1(P):
    A, rest = {}, {}
    for (m, i), c in P.items():
        e = expo(m, T1)
        if e: A[(with_(m, T1, e - 1), i)] = A.get((with_(m, T1, e - 1), i), 0) + c
        else: rest[(m, i)] = c
    return A, rest                                             # P = T1*A + rest
def split_T2(P):
    """P = (T2 - 1)*A + P|_{T2=1}"""
    by = {}
    for (m, i), c in P.items(): by.setdefault((drop(m, T2), i), {})[expo(m, T2)] = c
    A, rest = {}, {}
    for (m0, i), d in by.items():
        deg = max(d); a = [d.get(j, 0) for j in range(deg + 1)]
        # synthetic division by (T2 - 1): q_{j-1} = a_j + q_j
        q = [0] * deg; acc = 0
        for j in range(deg, 0, -1):
            acc = a[j] + acc; q[j - 1] = acc
        r = a[0] + (q[0] if deg else 0)
        for j, c in enumerate(q):
            if c: A[(with_(m0, T2, j), i)] = A.get((with_(m0, T2, j), i), 0) + c
        if r: rest[(m0, i)] = rest.get((m0, i), 0) + r
    return A, rest
def split_S2(P, d):
    """Dk^d * P = X*A + P3,  P3 = sum_j p_j Nk^j Dk^(d-j)   (S2-degree of P <= d)"""
    by = {}
    for (m, i), c in P.items(): by.setdefault(expo(m, S2), {})[(drop(m, S2), i)] = c
    A, P3 = {}, {}
    Xp = [const(1)]
    for k in range(1, d + 1): Xp.append(imul(Xp[-1], X))
    Nkp = [const(1)]
    for k in range(1, d + 1): Nkp.append(imul(Nkp[-1], Nk))
    for j, pj in by.items():
        assert j <= d
        base = iscale(pj, Dk ** (d - j))
        P3 = iadd(P3, imul(base, Nkp[j]))
        for k in range(1, j + 1):            # (Dk S2)^j = sum_k C(j,k) X^k Nk^(j-k)
            A = iadd(A, imul(iscale(base, comb(j, k)), imul(Xp[k - 1], Nkp[j - k])))
    return A, P3
# ---------- A1: e_sq = D_O * No1 * X^2 from ek_Omega, T2 - 1, R
DO = EK["Omega"][0]
P = iscale(facts["ek_Omega"], Do1 * Dk * Dk)                   # Do1 Dk^2 D_O Omega
A2_, rest = split_T2(P)                                        # P = (T2-1) A2 + P|T2=1
target = iscale(imul(No1, imul(X, X)), DO)                     # D_O No1 X^2
Bq = divR(iadd(rest, target, -1))                              # rest - target = R * Bq  (Omega = o1 (S2-kappa)^2 mod R)
cl = [(const(Do1 * Dk * Dk), "ek_Omega"), (iscale(A2_, -1), "eT2"), (iscale(Bq, -1), "eR")]
facts["e_sq"] = target; check(target, cl); steps.append(("s_sq", "e_sq", cl, True))
# ---------- A2: Bezout a No1 + b R = c
No1q = fmpq_poly([No1.get(((), i), 0) for i in range(5)])
g, s_, t_ = No1q.xgcd(Rr); assert g == 1
den = 1
for x in list(s_.coeffs()) + list(t_.coeffs()): den = lcm(den, int(fmpq(x).q))
a_ = {((), i): int(fmpq(x) * den) for i, x in enumerate(s_.coeffs()) if fmpq(x) != 0}
b_ = {((), i): int(fmpq(x) * den) for i, x in enumerate(t_.coeffs()) if fmpq(x) != 0}
cB = den
assert iadd(imul(a_, No1), imul(b_, eR)) == const(cB)
X2 = imul(X, X)
tgt2 = iscale(X2, cB * DO)                                     # c D_O X^2
cl = [(a_, "e_sq"), (iscale(imul(b_, X2), DO), "eR")]
check(tgt2, cl); steps.append(("s_X2", ("X2", cB * DO), cl, False))
# ---------- B1: slice facts
slice_facts = {}
for n in NAMES:
    P = facts[f"ek_{n}"]
    d = max(expo(m, S2) for (m, i) in P)
    A1, r1 = split_T1(P)
    A2, r2 = split_T2(r1)
    A3, r3 = split_S2(r2, d)                                   # Dk^d r2 = X A3 + r3
    f = modR(r3); A4 = divR(iadd(r3, f, -1))
    # Dk^d P = Dk^d T1 A1 + Dk^d (T2-1) A2 + X A3 + f + R A4
    cl = [(const(Dk ** d), f"ek_{n}"), (iscale(A1, -(Dk ** d)), "eT1"), (iscale(A2, -(Dk ** d)), "eT2"),
          (iscale(A3, -1), "eX"), (iscale(A4, -1), "eR")]
    facts[f"f_{n}"] = f; check(f, cl); steps.append((f"s_f_{n}", f"f_{n}", cl, True))
    slice_facts[n] = (d, f)
    assert all(expo(m, T1) == 0 and expo(m, T2) == 0 and expo(m, S2) == 0 for (m, i) in f)
# ---------- B2/B3: the step-1 slice certificate  1 = sum L_i F_i^slice  (F^slice = cond_n at T1=0, T2=1, S2=kappa)
cb = json.load(open(CERT))
assert cb["generators"] == NAMES
SV = [S1, R1, R2, Q]
L = []
for ci in cb["cofactors"]:
    P = {}
    for e, cs in ci:
        m = tuple(sorted((SV[k], x) for k, x in enumerate(e) if x))
        P[m] = mc.Kc(cs)
    L.append(P)
# f_n = Dk^d D_n cond_n|slice (mod R);  nu_n := DD * L_n / (Dk^d D_n)  integral
den = 1
for n, Ln in zip(NAMES, L):
    d, _ = slice_facts[n]; Dn = EK[n][0]
    for c in Ln.values():
        for i in range(5):
            if c[i] != 0:
                q = Fraction(int(c[i].p), int(c[i].q)) / (Dk ** d * Dn); den = lcm(den, q.denominator)
DD = den
parts = []
tot = {}
for n, Ln in zip(NAMES, L):
    d, f = slice_facts[n]; Dn = EK[n][0]
    nu = {}
    for m, c in Ln.items():
        for i in range(5):
            if c[i] != 0:
                v = Fraction(int(c[i].p), int(c[i].q)) * DD / (Dk ** d * Dn); assert v.denominator == 1
                nu[(m, i)] = int(v)
    prod = imul(nu, f); p_ = modR(prod); qn = divR(iadd(prod, p_, -1))
    cl = [(nu, f"f_{n}"), (iscale(qn, -1), "eR")]
    facts[f"p_{n}"] = p_; check(p_, cl); steps.append((f"s_p_{n}", f"p_{n}", cl, True))
    tot = iadd(tot, p_)
    parts.append(f"p_{n}")
fin_rest = iadd(tot, const(DD), -1)                            # sum p_n - DD  ==  R * A5  (mod-R identity)
A5 = divR(fin_rest)
cl = [(const(1), p) for p in parts] + [(iscale(A5, -1), "eR")]
check(const(DD), cl); steps.append(("s_final", ("num", DD), cl, False))
print(f"certificates checked: Dk {Dk}, Bezout c {cB} ({len(str(cB))} digits), DD has {len(str(DD))} digits; slice S2-degrees",
      {n: slice_facts[n][0] for n in NAMES}, "; part sizes", {p: len(facts[p]) for p in parts})
