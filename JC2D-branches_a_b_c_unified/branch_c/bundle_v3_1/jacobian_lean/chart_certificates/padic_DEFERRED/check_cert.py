"""Independent check (no Singular) of the single-prime argument for the chart {T2 != 0} of lower_c's system.

Input : certgen_c/conds_c.json (lower_c's general conditions, exact over K5 = Q[w]/(R)),
        padic/cert_p{p}_w{r}.json (cofactors produced by Singular; only USED as data here).
Checks: E1  Omega = o1*(S2 - kappa*T2^2)^2 exactly (o2^2 = 4 o1 o3, o1 != 0)
        E2  Sq, Psi, Phi1, Phi2, Theta1..3 are weighted-homogeneous (weights T 1, S 2, R 3, Q 4)
        E3  no monomial Q^k (or constant): the vertex (0,...,0,1) is an exact zero
        E4  Jacobian of the Q=1 slice at the vertex has rank 5 < 6 over K5 (and structurally <= 5)
        P0  R(r) = 0, R'(r) != 0 mod p            (Hensel: w_p in Z_p with w_p = r mod p)
        P1  all coefficients (and kappa) are p-integral
        P2  v^N = sum_i c_i * f_i(T,S,R,0)  in F_p[T,S,R]  for v = T1..R2        (cone meets Q=0 only at 0)
        P3  g_j = sum_i c_i * f_i(T,S,R,1)  in F_p[T,S,R],  {g_j} = {T1-cT2, S1, S2, R1, R2, T2^2}   (dim <= 2)
Each identity is checked by exact expansion (flint nmod_mpoly) AND by evaluation at random points with plain ints."""
import json, sys, random, re
from fractions import Fraction as F
from flint import fmpq_poly, fmpq, nmod_mpoly_ctx
sys.set_int_max_str_digits(0)
V = ["b_11_20", "b_12_22", "b_11_21", "b_12_23", "a_6_13", "a_7_15", "b_10_21"]
SH = ["T1", "T2", "S1", "S2", "R1", "R2", "Q"]
WT = [1, 1, 2, 2, 3, 3, 4]
Rpoly = [26, 0, 3, 3, -1, 1]
Rr = fmpq_poly(Rpoly)
NAMES = ["Psi", "Phi1", "Phi2", "Theta1", "Theta2", "Theta3"]
def Kel(cs): return fmpq_poly([fmpq(*map(int, c.split('/'))) if '/' in c else fmpq(int(c)) for c in cs]) % Rr
def kinv(a):
    g, s, _ = a.xgcd(Rr); assert g == 1; return s % Rr
def fails(msg): print("FAIL:", msg); sys.exit(1)

def exact_checks(d):
    Om = {tuple(sorted((v, e) for v, e in m)): Kel(cs) for m, cs in d["Omega"]}
    if len(Om) != 3: fails("Omega has unexpected support")
    o1 = Om[(("b_12_23", 2),)]; o2 = Om[(("b_12_22", 2), ("b_12_23", 1))]; o3 = Om[(("b_12_22", 4),)]
    if o1 == 0 or (o2 * o2 - 4 * o1 * o3) % Rr != 0: fails("E1")
    kap = (-o2 * kinv(2 * o1)) % Rr
    print("E1 ok: Omega = o1 (S2 - kappa T2^2)^2 exactly, o1 != 0")
    polys = {}
    for n in NAMES:
        P = {}
        for m, cs in d[n]:
            e = [0] * 7
            for v, k in m: e[V.index(v)] = k
            P[tuple(e)] = Kel(cs)
        polys[n] = P
        ws = {sum(a * b for a, b in zip(e, WT)) for e in P}
        if len(ws) != 1: fails(f"E2 {n}")
        if any(sum(e[:6]) == 0 for e in P): fails(f"E3 {n}")
    print("E2 ok: weights", {n: sum(a * b for a, b in zip(next(iter(polys[n])), WT)) for n in NAMES}, "(Sq: 2)")
    print("E3 ok: no Q^k or constant monomial in Sq, Psi, Phi1, Phi2, Theta1..3")
    # E4: linear part at the vertex of the Q=1 slice: coefficient of v * Q^k
    rows = [[Kel(["0"])] * 3 + [Kel(["1"])] + [Kel(["0"])] * 2]              # Sq: dS2
    for n in NAMES:
        r = [Kel(["0"])] * 6
        for e, c in polys[n].items():
            if sum(e[:6]) == 1: r[[i for i in range(6) if e[i] == 1][0]] = c
        rows.append(r)
    M = [row[:] for row in rows]; rk = 0
    for c in range(6):
        piv = next((i for i in range(rk, len(M)) if M[i][c] != 0), None)
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]; inv = kinv(M[rk][c])
        for i in range(len(M)):
            if i != rk and M[i][c] != 0:
                f = (M[i][c] * inv) % Rr; M[i] = [(M[i][j] - f * M[rk][j]) % Rr for j in range(6)]
        rk += 1
    wt5 = [n for n in NAMES if sum(a * b for a, b in zip(next(iter(polys[n])), WT)) == 5]
    if rk >= 6: fails("E4")
    print(f"E4 ok: Jacobian rank at the vertex over K5 = {rk} < 6 (weight-5 conditions: {wt5}, so the T-columns have rank <= 1)")
    return polys, kap

def red(a, p, r):                                  # K5 element -> F_p at w = r; asserts p-integrality (P1)
    t = 0
    for k, c in enumerate(a.coeffs()):
        c = fmpq(c); num, den = int(c.p), int(c.q)
        if den % p == 0: fails(f"P1: denominator divisible by {p}")
        t = (t + num * pow(den, -1, p) * pow(r, k, p)) % p
    return t

TERM = re.compile(r"([+-]?)([^+-]+)")
def parse(s, names, p):                            # Singular polynomial string -> dict(exponent tuple -> coeff mod p)
    s = s.replace(" ", "")
    out = {}
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

def check_prime(polys, kap, p, r, cert, perturb=None):
    if sum(c * pow(r, k, p) for k, c in enumerate(Rpoly)) % p != 0: fails("P0 root")
    if sum(k * c * pow(r, k - 1, p) for k, c in enumerate(Rpoly) if k) % p == 0: fails("P0 simple")
    kp = red(kap, p, r)
    # generators mod p in the 7 variables, as dicts
    gens = {"Sq": {(0, 0, 0, 1, 0, 0, 0): 1, (0, 2, 0, 0, 0, 0, 0): (-kp) % p}}
    for n in NAMES: gens[n] = {e: v for e, c in polys[n].items() if (v := red(c, p, r))}
    order = ["Sq"] + NAMES
    print(f"p={p}, r={r}: P0 ok (simple root), P1 ok (p-integral)")
    X6 = SH[:6]
    ctx = nmod_mpoly_ctx.get(tuple(X6), modulus=p, ordering="degrevlex")
    def sub(P, q):                                  # substitute Q = q, drop to 6 variables
        out = {}
        for e, c in P.items():
            if q == 0 and e[6]: continue
            out[e[:6]] = (out.get(e[:6], 0) + c) % p
        return {k: v for k, v in out.items() if v}
    rng = random.Random(p)
    pts = [[rng.randrange(p) for _ in range(6)] for _ in range(3)]
    def ev(P, x):
        t = 0
        for e, c in P.items():
            m = c
            for xi, k in zip(x, e):
                if k: m = m * pow(xi, k, p) % p
            t = (t + m) % p
        return t
    def verify(tag, lhs, cof, gs):
        cofd = [parse(c, X6, p) for c in cof]
        if perturb is not None and tag == perturb:
            k = next(i for i, c in enumerate(cofd) if c); e0 = next(iter(cofd[k])); cofd[k][e0] = (cofd[k][e0] + 1) % p
        s = ctx.from_dict({}) if False else ctx.from_dict({(0,) * 6: 0})
        for cd, g in zip(cofd, gs):
            if cd: s += ctx.from_dict(cd) * ctx.from_dict(g)
        ok_exact = (s == ctx.from_dict(lhs) if lhs else s.is_zero())
        ok_eval = all(sum(ev(cd, x) * ev(g, x) for cd, g in zip(cofd, gs)) % p == ev(lhs, x) for x in pts)
        return ok_exact, ok_eval, sum(len(c) for c in cofd)
    g0 = [sub(gens[n], 0) for n in order]
    for e in cert["P2"]:
        v = X6.index(e["var"]); lhs = {tuple(e["N"] if i == v else 0 for i in range(6)): 1}
        ok, ok2, nt = verify(f"P2:{e['var']}", lhs, e["cof"], g0)
        print(f"   P2 {e['var']}^{e['N']} in J6|Q=0 : exact {ok}, random-eval {ok2}  ({nt} cofactor terms)")
        if not (ok and ok2): return False
    g1 = [sub(gens[n], 1) for n in order]
    targets = []
    for e in cert["P3"]:
        lhs = parse(e["g"], X6, p)
        if not lhs: continue
        ok, ok2, nt = verify(f"P3:{e['g']}", lhs, e["cof"], g1)
        print(f"   P3 {e['g']:>16s} in J6|Q=1 : exact {ok}, random-eval {ok2}  ({nt} cofactor terms)")
        if not (ok and ok2): return False
        targets.append(lhs)
    # structure: every variable except T2 is (v - c T2) or v, and T2^2 is present  =>  k[x]/(g) spanned by {1, T2}
    T2 = X6.index("T2"); unit = lambda i: tuple(1 if j == i else 0 for j in range(6))
    lin = {}
    for g in targets:
        if all(sum(e) == 1 for e in g) and any(e == unit(i) and c == 1 for i in range(6) if i != T2 for e, c in g.items()):
            i = next(i for i in range(6) if i != T2 and g.get(unit(i)) == 1)
            if set(g) <= {unit(i), unit(T2)}: lin[i] = g
    has_sq = any(g == {tuple(2 if j == T2 else 0 for j in range(6)): 1} for g in targets)
    if sorted(lin) != [i for i in range(6) if i != T2] or not has_sq: fails("P3 structure")
    print("   P3 structure ok: (T1 - c T2, S1, S2, R1, R2, T2^2) inside J6|Q=1  =>  dim_k k[x]/(J6|Q=1) <= 2")
    return True

if __name__ == "__main__":
    d = json.load(open("certgen_c/conds_c.json"))
    polys, kap = exact_checks(d)
    for p, r in [(1000003, 806739), (32003, 11147)]:
        cert = json.load(open(f"padic/cert_p{p}_w{r}.json"))
        if not check_prime(polys, kap, p, r, cert): fails(f"certificate at p={p}")
        print(f"p={p}: ALL CHECKS PASSED")
    # negative controls
    p, r = 1000003, 806739; cert = json.load(open(f"padic/cert_p{p}_w{r}.json"))
    import io, contextlib
    for tag, kw in [("perturbed cofactor (P2:T1)", dict(perturb="P2:T1")), ("perturbed cofactor (P3:S1)", dict(perturb="P3:S1"))]:
        with contextlib.redirect_stdout(io.StringIO()): res = check_prime(polys, kap, p, r, cert, **kw)
        print(f"control, {tag}: check returns {res} (expected False)")
    # control: the certificate for the root 11147 of R mod 32003, checked at the other root 16284 -> must fail
    c2 = json.load(open("padic/cert_p32003_w11147.json"))
    with contextlib.redirect_stdout(io.StringIO()): res = check_prime(polys, kap, 32003, 16284, c2)
    print(f"control, certificate checked at the wrong root of R mod 32003: check returns {res} (expected False)")
