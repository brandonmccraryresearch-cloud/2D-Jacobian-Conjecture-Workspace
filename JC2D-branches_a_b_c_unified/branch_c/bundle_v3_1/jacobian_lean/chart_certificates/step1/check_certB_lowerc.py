"""Independent exact check of step1/certB_lowerc.json:  1 = sum_i L_i F_i  in K5[S1,R1,R2,Q],  F_i = lower_c's
Psi, Phi1, Phi2, Theta1..3 at T1 = 0, T2 = 1, S2 = kappa.
Independent of the producer: the substitution is re-implemented here, and the product is expanded in
Q[w][S1,R1,R2,Q] with fmpq_mpoly (w an ordinary variable) and reduced mod R(w) only at the end.
Negative controls: a perturbed coefficient; Theta3 dropped; the pipeline's generators (audit_fix.pkl) in place of lower_c's."""
import json, sys, os, pickle
from flint import fmpq, fmpq_mpoly_ctx, fmpq_poly
sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
ctx = fmpq_mpoly_ctx.get(("S1", "R1", "R2", "Q", "w"), ordering="lex")
Rw = ctx.from_dict({(0, 0, 0, 0, 5): 1, (0, 0, 0, 0, 4): -1, (0, 0, 0, 0, 3): 3, (0, 0, 0, 0, 2): 3, (0, 0, 0, 0, 0): 26})
def q(c): return fmpq(*map(int, c.split('/'))) if '/' in c else fmpq(int(c))
def kel(cs):                                                   # K5 element as a polynomial in w
    return ctx.from_dict({(0, 0, 0, 0, k): q(c) for k, c in enumerate(cs) if q(c) != 0}) if any(q(c) != 0 for c in cs) else ctx.from_dict({})
def reduce_w(P):                                               # remainder mod R(w) (R monic in w)
    Rp = fmpq_poly([26, 0, 3, 3, -1, 1]); out = {}
    by = {}
    for e, c in P.to_dict().items():
        by.setdefault(e[:4], {})[e[4]] = c
    for m, wd in by.items():
        f = fmpq_poly([wd.get(k, 0) for k in range(max(wd) + 1)]) % Rp
        for k, c in enumerate(f.coeffs()):
            if c != 0: out[m + (k,)] = c
    return ctx.from_dict(out) if out else ctx.from_dict({})
V7 = ["b_11_20", "b_12_22", "b_11_21", "b_12_23", "a_6_13", "a_7_15", "b_10_21"]
d = json.load(open(os.path.join(HERE, "..", "certgen_c", "conds_c.json")))
def generators(polys7, kap_w):
    """polys7: name -> {7-exponent: K5 poly in w (ctx element)};  T1 = 0, T2 = 1, S2 = kappa."""
    F = []
    for n in ["Psi", "Phi1", "Phi2", "Theta1", "Theta2", "Theta3"]:
        acc = ctx.from_dict({})
        for e, c in polys7[n].items():
            T1, T2, S1, S2, R1, R2, Qv = e
            if T1: continue
            acc += c * kap_w ** S2 * ctx.from_dict({(S1, R1, R2, Qv, 0): 1})
        F.append(reduce_w(acc))
    return F
def lowerc_polys():
    out = {}
    for n, P in d.items():
        Q = {}
        for m, cs in P:
            e = [0] * 7
            for v, k in m: e[V7.index(v)] += k
            Q[tuple(e)] = kel(cs)
        out[n] = Q
    return out
def kappa_w(polys7):                                           # kappa = -o2/(2 o1), inverse computed in K5 with fmpq_poly
    Om = polys7["Omega"]; Rp = fmpq_poly([26, 0, 3, 3, -1, 1])
    tofp = lambda P: fmpq_poly([P.to_dict().get((0, 0, 0, 0, k), 0) for k in range(5)])
    o1, o2, o3 = tofp(Om[(0,0,0,2,0,0,0)]), tofp(Om[(0,2,0,1,0,0,0)]), tofp(Om[(0,4,0,0,0,0,0)])
    assert (o2 * o2 - 4 * o1 * o3) % Rp == 0 and o1 % Rp != 0
    g, s, _ = (2 * o1).xgcd(Rp); assert g == 1
    k = (-o2 * s) % Rp
    return ctx.from_dict({(0, 0, 0, 0, i): c for i, c in enumerate(k.coeffs()) if c != 0})
cert = json.load(open(os.path.join(HERE, "certB_lowerc.json")))
def cofactors(perturb=False):
    L = []
    for ci in cert["cofactors"]:
        acc = {}
        for m, cs in ci:
            for k, c in enumerate(cs):
                if q(c) != 0: acc[tuple(m) + (k,)] = q(c)
        L.append(acc)
    if perturb:
        e0 = next(iter(L[0])); L[0][e0] = L[0][e0] + 1
    return [ctx.from_dict(a) if a else ctx.from_dict({}) for a in L]
def check(F, L, drop=None):
    S = ctx.from_dict({})
    for i, (Fi, Li) in enumerate(zip(F, L)):
        if i != drop: S += Li * Fi
    return reduce_w(S) == ctx.from_dict({(0, 0, 0, 0, 0): 1})
P7 = lowerc_polys(); kw = kappa_w(P7); F = generators(P7, kw)
print("generators (terms, w expanded):", [len(f.to_dict()) for f in F])
L = cofactors()
print("certificate: 1 = sum L_i F_i exactly in K5[S1,R1,R2,Q]:", check(F, L))
print("control, one coefficient perturbed (expect False):", check(F, cofactors(perturb=True)))
print("control, Theta3 dropped (expect False):", check(F, L, drop=5))
AUD = os.path.join(os.environ.get("AUDIT_DIR", os.path.join(HERE, "..", "..", "audit_repro")), "audit_fix.pkl")
if os.path.exists(AUD):
    a = pickle.load(open(AUD, "rb")); pp = {}
    for n, m in [("Omega", "Omega"), ("Psi", "Psi"), ("Phi1", "Phi1"), ("Phi2", "Phi2"), ("Th1", "Theta1"), ("Th2", "Theta2"), ("Th3", "Theta3")]:
        src = a["Omega"] if n == "Omega" else a["polys"][n]
        pp[m] = {tuple(e): kel(c) for e, c in src.items()}
    Fp = generators(pp, kappa_w(pp))
    print("control, the pipeline's generators with this certificate (expect False):", check(Fp, L))
