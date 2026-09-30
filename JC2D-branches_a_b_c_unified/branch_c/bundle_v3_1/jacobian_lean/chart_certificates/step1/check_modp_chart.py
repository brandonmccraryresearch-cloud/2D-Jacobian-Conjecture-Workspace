"""Singular-free check of the modular chart certificates for lower_c's ideal (T2 = 1, S2 = kappa):
   chartcert_p{p}_w{r}.json :  sum_i L_i F_i == 1          in F_p[T1,S1,R1,R2,Q]        (w = r)
   chartcert_p109_inert.json:  L_R R(w) + sum_i L_i F_i == 1 in F_109[T1,S1,R1,R2,Q,w]
Generators rebuilt here from certgen_c/conds_c.json (own substitution code); identities checked by exact
expansion (nmod_mpoly) and by evaluation at random points with plain integers; three negative controls."""
import json, sys, os, re, random
from fractions import Fraction as Fr
from flint import nmod_mpoly_ctx
sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
V7 = ["b_11_20", "b_12_22", "b_11_21", "b_12_23", "a_6_13", "a_7_15", "b_10_21"]
NAMES = ["Psi", "Phi1", "Phi2", "Theta1", "Theta2", "Theta3"]
RC = [26, 0, 3, 3, -1, 1]
d = json.load(open(os.path.join(HERE, "..", "certgen_c", "conds_c.json")))
def coeffs(cs, p):                                           # K5 element -> list of its 5 power-basis coords mod p
    out = []
    for c in cs:
        f = Fr(c)
        if f.denominator % p == 0: raise SystemExit(f"FAIL: coefficient not {p}-integral")
        out.append(f.numerator * pow(f.denominator, -1, p) % p)
    return out
def wpoly_mul(a, b, p):                                      # multiply polynomials in w (lists) and reduce mod R(w)
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): c[i + j] = (c[i + j] + x * y) % p
    for k in range(len(c) - 1, 4, -1):                       # w^5 = w^4 - 3w^3 - 3w^2 - 26
        t = c[k]; c[k] = 0
        if t:
            for j in range(5): c[k - 5 + j] = (c[k - 5 + j] - t * RC[j]) % p
    return (c + [0] * 5)[:5]
def wpoly_inv(a, p):                                         # inverse in F_p[w]/(R) by solving a*x = 1 (5x5 linear system)
    cols = []
    for j in range(5):
        e = [0] * 5; e[j] = 1; cols.append(wpoly_mul(a, e, p))
    M = [[cols[j][i] for j in range(5)] + [1 if i == 0 else 0] for i in range(5)]
    for c in range(5):
        piv = next(i for i in range(c, 5) if M[i][c]); M[c], M[piv] = M[piv], M[c]
        iv = pow(M[c][c], -1, p); M[c] = [x * iv % p for x in M[c]]
        for i in range(5):
            if i != c and M[i][c]:
                f = M[i][c]; M[i] = [(x - f * y) % p for x, y in zip(M[i], M[c])]
    return [M[i][5] for i in range(5)]
def generators(p):
    """-> name -> dict {(T1,S1,R1,R2,Q,wpow): coeff mod p}  (chart T2 = 1, S2 = kappa, w kept symbolic mod R)"""
    P7 = {}
    for n, P in d.items():
        Q = {}
        for m, cs in P:
            e = [0] * 7
            for v, k in m: e[V7.index(v)] += k
            Q[tuple(e)] = coeffs(cs, p)
        P7[n] = Q
    Om = P7["Omega"]; o1, o2, o3 = Om[(0,0,0,2,0,0,0)], Om[(0,2,0,1,0,0,0)], Om[(0,4,0,0,0,0,0)]
    kap = [(-x) % p for x in wpoly_mul(o2, wpoly_inv([2 * x % p for x in o1], p), p)]
    chk = [(a + b + c) % p for a, b, c in zip(wpoly_mul(o1, wpoly_mul(kap, kap, p), p), wpoly_mul(o2, kap, p), o3)]
    if any(chk): raise SystemExit("FAIL: kappa is not a root of Omega mod p")
    out = {}
    for n in NAMES:
        acc = {}
        for (T1, T2, S1, S2, R1, R2, Qv), c in P7[n].items():
            val = c
            for _ in range(S2): val = wpoly_mul(val, kap, p)
            for k, x in enumerate(val):
                if x:
                    key = (T1, S1, R1, R2, Qv, k); acc[key] = (acc.get(key, 0) + x) % p
        out[n] = {k: v for k, v in acc.items() if v}
    return out
TERM = re.compile(r"([+-]?)([^+-]+)")
def parse(s, names, p):
    s = s.replace(" ", ""); out = {}
    if s == "0": return out
    for sign, body in TERM.findall(s):
        coef, e = 1, [0] * len(names)
        for fac in body.split("*"):
            if fac.isdigit(): coef *= int(fac)
            else:
                v, _, k = fac.partition("^"); e[names.index(v)] += int(k) if k else 1
        coef = (-coef if sign == "-" else coef) % p
        out[tuple(e)] = (out.get(tuple(e), 0) + coef) % p
    return {k: v for k, v in out.items() if v}
def specialize(G, p, r):                                     # w -> r
    out = {}
    for e, c in G.items():
        k = e[:5]; out[k] = (out.get(k, 0) + c * pow(r, e[5], p)) % p
    return {k: v for k, v in out.items() if v}
def ev(P, x, p):
    t = 0
    for e, c in P.items():
        m = c
        for xi, k in zip(x, e):
            if k: m = m * pow(xi, k, p) % p
        t = (t + m) % p
    return t
def check(p, r, cert, perturb=False, drop=None, wrong_root=None):
    G = generators(p)
    X = ["T1", "S1", "R1", "R2", "Q"] + ([] if r is not None else ["w"])
    ctx = nmod_mpoly_ctx.get(tuple(X), modulus=p, ordering="degrevlex")
    if r is not None:
        gens = [specialize(G[n], p, wrong_root if wrong_root is not None else r) for n in NAMES]
    else:
        gens = [{(0, 0, 0, 0, 0, k): c % p for k, c in enumerate(RC) if c % p}] + [G[n] for n in NAMES]
    cof = [parse(s, X, p) for s in cert]
    if len(cof) != len(gens): raise SystemExit("FAIL: cofactor count")
    if perturb:
        k = next(i for i, c in enumerate(cof) if c); e0 = next(iter(cof[k])); cof[k][e0] = (cof[k][e0] + 1) % p
    S = ctx.from_dict({(0,) * len(X): 0})
    for i, (c, g) in enumerate(zip(cof, gens)):
        if c and g and i != drop: S += ctx.from_dict(c) * ctx.from_dict(g)
    exact = S == ctx.from_dict({(0,) * len(X): 1})
    rng = random.Random(p)
    pts = [[rng.randrange(p) for _ in X] for _ in range(3)]
    evok = all(sum(ev(c, x, p) * ev(g, x, p) for i, (c, g) in enumerate(zip(cof, gens)) if i != drop) % p == 1 for x in pts)
    return exact, evok, sum(len(c) for c in cof)
if __name__ == "__main__":
    ok_all = True
    for p, r, f in [(101, 9, "chartcert_p101_w9.json"), (1000003, 806739, "chartcert_p1000003_w806739.json"),
                    (109, None, "chartcert_p109_inert.json")]:
        cert = json.load(open(os.path.join(HERE, f)))
        ex, evk, nt = check(p, r, cert)
        where = f"F_{p}[T1,S1,R1,R2,Q] at w = {r}" if r is not None else f"F_{p}[T1,S1,R1,R2,Q,w] with R(w) as a generator"
        print(f"{f}: 1 = sum L_i F_i in {where}: exact {ex}, random-eval {evk}  ({nt} cofactor terms)")
        ok_all &= ex and evk
        ctl = [check(p, r, cert, perturb=True)[:2], check(p, r, cert, drop=len(cert) - 1)[:2]]
        if r is not None:
            other = (r + 1) % p                                      # not a root of R: the specialisation is wrong
            ctl.append(check(p, r, cert, wrong_root=other)[:2])
        print(f"   controls (perturbed / Theta3 dropped{' / other w' if r is not None else ''}): {ctl}  (expect all False)")
        ok_all &= not any(a or b for a, b in ctl)
    print("ALL MODULAR CHART CERTIFICATES PASSED" if ok_all else "FAILURE")
