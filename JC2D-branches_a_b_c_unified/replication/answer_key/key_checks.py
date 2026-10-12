"""
key_checks.py -- recompute, from scratch, the expected values of ANSWER_KEY.md that are cheap to compute.

DO NOT READ OR RUN THIS BEFORE YOU HAVE RECORDED YOUR OWN RESULTS (see ../INDEPENDENT_REPLICATION_GUIDE.md).

It is the project's check that the answer key is right. It shares no code with the project's pipelines: the polygons,
the bracket and the layer systems are rebuilt here with sympy; K5 arithmetic is python-flint. Only input data are read
from the repository:
  - the K5 top-layer point, key "top" of branches_a_b/lean/certgen/cert.json;
  - the twelve branch-(c) conditions, branch_c/bundle_v3_1/jacobian_lean/certgen_c/conds_c.json;
  - the weight-0 row without new unknowns, key "Xtra1" of branch_c/bundle_v3_1/jacobian_lean/certgen_c/cert_c.json.

Prints one line per checked value; the last line is "ANSWER KEY CHECKS: n passed, m failed".
Runtime about 15 s; needs python3 with sympy and python-flint. Run: python3 key_checks.py
"""
import json, os, sys
from fractions import Fraction
from itertools import combinations
import sympy as sp
from flint import fmpq_poly, fmpq

HERE = os.path.dirname(os.path.abspath(__file__))
UNI = os.path.abspath(os.path.join(HERE, "..", ".."))
CERT = os.path.join(UNI, "branches_a_b", "lean", "certgen", "cert.json")
CONDS = os.path.join(UNI, "branch_c", "bundle_v3_1", "jacobian_lean", "certgen_c", "conds_c.json")
ok = [0, 0]
def check(cond, label, value):
    print(("PASS  " if cond else "FAIL  ") + f"{label}: {value}")
    ok[0 if cond else 1] += 1

# ------------------------------------------------------------------ polygons (own point-in-polygon test)
def lattice(verts):
    """integer points of the convex hull of verts (closed); hull by gift wrapping, test by cross products"""
    pts = sorted(set(verts))
    def cross(o, a, b): return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])
    lower, upper = [], []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0: lower.pop()
        lower.append(p)
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0: upper.pop()
        upper.append(p)
    hull = lower[:-1] + upper[:-1]
    xs = [v[0] for v in verts]; ys = [v[1] for v in verts]
    out = []
    for i in range(min(xs), max(xs) + 1):
        for j in range(min(ys), max(ys) + 1):
            if all(cross(hull[k], hull[(k+1) % len(hull)], (i, j)) >= 0 for k in range(len(hull))):
                out.append((i, j))
    return out
NP_ab = [(0, 0), (1, 0), (8, 14), (8, 16)]; NQ_ab = [(0, 0), (2, 1), (12, 21), (12, 24)]
NP_c = NP_ab + [(0, 8)]; NQ_c = NQ_ab + [(0, 12)]
LPab, LQab, LPc, LQc = lattice(NP_ab), lattice(NQ_ab), lattice(NP_c), lattice(NQ_c)
check(len(LPab) == 25 and len(LQab) == 47, "R1 (a,b) lattice points |N(P)|, |N(Q)|", (len(LPab), len(LQab)))
check(len(LPc) == 61 and len(LQc) == 125, "C1 (c) lattice points |N(P)|, |N(Q)|", (len(LPc), len(LQc)))
# second count: the polygons as explicit half-planes (edges read off the vertex lists by hand)
HP = {"P_ab": lambda i, j: 0 <= i <= 8 and 0 <= j and 2 * i - 2 <= j <= 2 * i,
      "Q_ab": lambda k, l: 0 <= k <= 12 and k <= 2 * l and 2 * k - 3 <= l <= 2 * k,
      "P_c": lambda i, j: 0 <= i <= 8 and 0 <= j and 2 * i - 2 <= j <= i + 8,
      "Q_c": lambda k, l: 0 <= k <= 12 and k <= 2 * l and 2 * k - 3 <= l <= k + 12}
HPpts = {n: sorted((i, j) for i in range(13) for j in range(25) if f(i, j)) for n, f in HP.items()}
same = [HPpts["P_ab"] == sorted(LPab), HPpts["Q_ab"] == sorted(LQab), HPpts["P_c"] == sorted(LPc), HPpts["Q_c"] == sorted(LQc)]
check(all(same), "R1/C1 hull code and half-plane description give the same lattice points", same)
def pair_count(LP, LQ):
    """weights of the monomials of [P,Q] by pairs of terms (no cancellation: distinct pairs, distinct products)"""
    mons = {(i + k - 1, j + l - 1) for i, j in LP for k, l in LQ if i * l - j * k != 0}
    from collections import Counter as C_
    return dict(C_(2 * a - b for a, b in mons))

# ------------------------------------------------------------------ the bracket, by sympy differentiation
x, y = sp.symbols("x y")
def bracket_coeffs(LP, LQ):
    A = {(i, j): sp.Symbol(f"a_{i}_{j}") for i, j in LP}
    B = {(k, l): sp.Symbol(f"b_{k}_{l}") for k, l in LQ}
    P = sum(s * x**i * y**j for (i, j), s in A.items()); Q = sum(s * x**k * y**l for (k, l), s in B.items())
    J = sp.Poly(sp.expand(sp.diff(P, x) * sp.diff(Q, y) - sp.diff(P, y) * sp.diff(Q, x)), x, y)
    return {m: c for m, c in J.terms() if c != 0}, A, B
Jab, Aab, Bab = bracket_coeffs(LPab, LQab)
wt = lambda m: 2 * m[0] - m[1]
from collections import Counter
# R1: unknowns by depth (P layer 2i-j, top 2; Q layer 2k-l, top 3), and the unknowns that never occur
occ_ab = {str(s_) for c in Jab.values() for s_ in c.free_symbols}
never_ab = sorted({str(s_) for s_ in list(Aab.values()) + list(Bab.values())} - occ_ab)
check(never_ab == ["a_0_0", "b_0_0"], "R1 (a,b) unknowns that never occur in [P,Q]", never_ab)
dep_ab = Counter(2 - (2 * i - j) for i, j in LPab if (i, j) != (0, 0))
dep_ab.update(3 - (2 * k - l) for k, l in LQab if (k, l) != (0, 0))
check(dict(dep_ab) == {0: 19, 1: 19, 2: 20, 3: 12}, "R1 (a,b) occurring unknowns by depth (0 = top layer)", dict(sorted(dep_ab.items())))
cab = Counter(wt(m) for m in Jab)
check(dict(cab) == {4: 17, 3: 18, 2: 19, 1: 19, 0: 19}, "R2 (a,b) nonzero coefficients of [P,Q] by weight 2A-B", dict(sorted(cab.items(), reverse=True)))
check(pair_count(LPab, LQab) == dict(cab), "R2 (a,b) the same count from pairs of terms", pair_count(LPab, LQab) == dict(cab))
# grading by depth (a_{i,j}: 2 - (2i - j), b_{k,l}: 3 - (2k - l)): every term of the weight-d equation has degree 4 - d,
# so the lower layers' solution set at a fixed top layer is a cone (used for R5, R6: a finite cone is {0})
def depth_of(s_):
    _, i, j = str(s_).split('_'); i, j = int(i), int(j)
    return 2 - (2 * i - j) if str(s_)[0] == 'a' else 3 - (2 * i - j)
def graded(J):
    for m, c in J.items():
        for term in sp.Add.make_args(sp.expand(c)):
            _, syms = term.as_coeff_mul()
            if sum(depth_of(s_) for s_ in syms) != 4 - wt(m): return False
    return True
g_ab = graded(Jab)
check(g_ab, "R5/R6 (a,b) the weight-d equation is homogeneous of degree 4 - d in the depth grading", g_ab)
Jc, Ac, Bc = bracket_coeffs(LPc, LQc)
cc = Counter(wt(m) for m in Jc)
check(sum(cc.values()) == 302 and sum(v for d, v in cc.items() if -3 <= d <= 3) == 132,
      "C1 (c) nonzero coefficients: total, and weights 3..-3", (sum(cc.values()), sum(v for d, v in cc.items() if -3 <= d <= 3)))
WANT_CC = {4: 17, 3: 18, 2: 19, 1: 19, 0: 20, -1: 19, -2: 19, -3: 18, -4: 17, -5: 16, -6: 15, -7: 14, -8: 13,
           -9: 12, -10: 11, -11: 10, -12: 9, -13: 8, -14: 7, -15: 6, -16: 5, -17: 4, -18: 3, -19: 2, -20: 1}
check(dict(cc) == WANT_CC, "C1 (c) nonzero coefficients by weight", dict(sorted(cc.items(), reverse=True)))
check(pair_count(LPc, LQc) == dict(cc), "C1 (c) the same count from pairs of terms", pair_count(LPc, LQc) == dict(cc))
low = [(m, sp.expand(c)) for m, c in Jc.items() if wt(m) == -20]
check(len(low) == 1 and low[0][0] == (0, 20) and sp.expand(low[0][1] - (-8 * sp.Symbol("a_0_8") * sp.Symbol("b_1_13")
      + 12 * sp.Symbol("a_1_9") * sp.Symbol("b_0_12"))) == 0, "C1 (c) the weight -20 equation (coefficient of y^20)", low)
occ_c = {str(s_) for c in Jc.values() for s_ in c.free_symbols}
never_c = sorted({str(s_) for s_ in list(Ac.values()) + list(Bc.values())} - occ_c)
check(never_c == ["a_0_0", "b_0_0"], "C1 (c) unknowns that never occur in [P,Q]", never_c)
g_c = graded(Jc)
check(g_c, "C2 (c) the weight-d equation is homogeneous of degree 4 - d in the depth grading", g_c)

# ------------------------------------------------------------------ K5 and the top-layer point
Rr = fmpq_poly([26, 0, 3, 3, -1, 1])
def K(c): return fmpq_poly([fmpq(Fraction(s).numerator, Fraction(s).denominator) for s in c]) % Rr
def kinv(a):
    g, s, _ = a.xgcd(Rr); assert g == 1; return s % Rr
cert = json.load(open(CERT)); top = {v: K(c) for v, c in cert["top"].items()}
depth = lambda v, top_d: top_d - (2 * int(v.split('_')[1]) - int(v.split('_')[2]))   # a: top weight 2, b: 3
def dep(v): return depth(v, 2) if v[0] == 'a' else depth(v, 3)
# E5 at the top point: lambda = 1
lam_ok = True
for m, c in Jab.items():
    if wt(m) != 4: continue
    val = fmpq_poly([0])
    for term in sp.Add.make_args(sp.expand(c)):
        coef, syms = term.as_coeff_mul()
        prod = fmpq_poly([fmpq(int(sp.numer(coef)), int(sp.denom(coef)))])
        for s_ in syms: prod = (prod * top[str(s_)]) % Rr
        val = (val + prod) % Rr
    target = fmpq_poly([1]) if m == (2, 0) else fmpq_poly([0])
    lam_ok &= (val == target)
check(lam_ok, "R3 input: the K5 point of cert.json solves E5 with lambda = 1", lam_ok)
# linear operators of E4, E3, E2: coefficients of the new unknowns, top values substituted
def operator(d_layer, new_depth):
    rows, cols = [], set()
    eqs = [c for m, c in sorted(Jab.items()) if wt(m) == d_layer]
    for c in eqs:
        for term in sp.Add.make_args(sp.expand(c)):
            for s_ in term.free_symbols:
                if str(s_) not in top and dep(str(s_)) == new_depth: cols.add(str(s_))
    cols = sorted(cols)
    M = []
    for c in eqs:
        row = []
        for v in cols:
            coef = sp.expand(sp.diff(c, sp.Symbol(v)))
            # keep only the part involving top variables alone (the operator), i.e. set lower unknowns to 0
            coef0 = coef.subs({s_: 0 for s_ in coef.free_symbols if str(s_) not in top})
            val = fmpq_poly([0])
            for term in sp.Add.make_args(sp.expand(coef0)):
                if term == 0: continue
                cf, syms = term.as_coeff_mul()
                prod = fmpq_poly([fmpq(int(sp.numer(cf)), int(sp.denom(cf)))])
                for s_ in syms: prod = (prod * top[str(s_)]) % Rr
                val = (val + prod) % Rr
            row.append(val)
        M.append(row)
    return M, cols
def rank_K5(M):
    M = [r[:] for r in M]; rk = 0; ncol = len(M[0]) if M else 0
    for c in range(ncol):
        piv = next((r for r in range(rk, len(M)) if M[r][c] != 0), None)
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]; iv = kinv(M[rk][c])
        for r in range(len(M)):
            if r != rk and M[r][c] != 0:
                f = (M[r][c] * iv) % Rr
                M[r] = [(a - f * b) % Rr for a, b in zip(M[r], M[rk])]
        rk += 1
    return rk
for d_layer, nd, name, want in ((3, 1, "E4", (18, 19, 17)), (2, 2, "E3", (19, 20, 18)), (1, 3, "E2", (19, 12, 12))):
    M, cols = operator(d_layer, nd)
    got = (len(M), len(cols), rank_K5(M))
    check(got == want, f"R4 {name} operator at the K5 point: rows x columns, rank over K5", got)

# ------------------------------------------------------------------ branch (c): layer operators at the K5 top layer
# at weight d the new unknowns are those of P-layer k = d - 2 and Q-layer l = d - 1 (k = 2i - j, l = 2k - l);
# the operator is the matrix of their coefficients with the top layer substituted (it involves nothing else)
def layer_of(v): return 2 * int(v.split('_')[1]) - int(v.split('_')[2])
def operator_c(d_layer):
    eqs = [c for m, c in sorted(Jc.items()) if wt(m) == d_layer]
    cols = sorted({str(s_) for c in eqs for s_ in c.free_symbols
                   if str(s_) not in top and ((str(s_)[0] == 'a' and layer_of(str(s_)) == d_layer - 2) or
                                             (str(s_)[0] == 'b' and layer_of(str(s_)) == d_layer - 1))})
    M = []
    for c in eqs:
        row = []
        for v in cols:
            coef = sp.expand(sp.diff(c, sp.Symbol(v)))
            val = fmpq_poly([0])
            for term in sp.Add.make_args(coef):
                if term == 0: continue
                cf, syms = term.as_coeff_mul()
                assert all(str(s_) in top for s_ in syms), (v, term)
                prod = fmpq_poly([fmpq(int(sp.numer(cf)), int(sp.denom(cf)))])
                for s_ in syms: prod = (prod * top[str(s_)]) % Rr
                val = (val + prod) % Rr
            row.append(val)
        M.append(row)
    zero_rows = sum(1 for r in M if all(x == 0 for x in r))
    return (len(M), len(cols), rank_K5(M), zero_rows)
WANT_C = {3: (18, 19, 17, 0), 2: (19, 20, 18, 0), 1: (19, 20, 18, 0), 0: (20, 19, 18, 1), -1: (19, 17, 17, 1),
          -2: (19, 15, 15, 2), -3: (18, 13, 13, 2)}
for d_layer, want in WANT_C.items():
    got = operator_c(d_layer)
    check(got == want, f"C2 (c) weight {d_layer:2d} operator: rows, new unknowns, rank over K5, rows without new unknowns", got)

# ------------------------------------------------------------------ branch (c): kappa and the chart generators mod p
conds = json.load(open(CONDS))
def kpoly(c): return K(c)
om = {tuple(sorted((v, e) for v, e in m)): kpoly(c) for m, c in conds["Omega"]}
o1 = om[(("b_12_23", 2),)]; o2 = om[(("b_12_22", 2), ("b_12_23", 1))]; o3 = om[(("b_12_22", 4),)]
check(((o2 * o2) % Rr) == ((4 * o1 * o3) % Rr), "C3 Omega is o1 (S2 - kappa T2^2)^2: o2^2 = 4 o1 o3 in K5", True)
kappa = (-o2 * kinv((2 * o1) % Rr)) % Rr
kap = [str(Fraction(int(kappa[i].p), int(kappa[i].q))) for i in range(5)]
check(kap == ["26267455159/851565312", "-7888899791/425782656", "16286392/1108809", "-2241077929/425782656", "1681963865/851565312"],
      "C3 kappa = -o2/(2 o1) in K5 (coefficients of 1, w, ..., w^4)", kap)
# torus-invariant form: kappa = 1/(3 b_12_21), i.e. Omega = 0 <=> b_12_22^2 = 3 b_12_21 b_12_23
check((kappa * 3 * top["b_12_21"]) % Rr == 1, "C2 kappa * 3 * b_12_21 = 1 (Omega = 0 <=> b_12_22^2 = 3 b_12_21 b_12_23)", True)
# the weight-0 equation without new unknowns (coefficient of x^19 y^38, after the higher layers are substituted;
# stored as Xtra1 by the project's make_cert_c.py) is a K5-multiple of Omega
CERTC = os.path.join(UNI, "branch_c", "bundle_v3_1", "jacobian_lean", "certgen_c", "cert_c.json")
xt = {tuple(sorted((v, e) for v, e in m)): kpoly(c) for m, c in json.load(open(CERTC))["Xtra1"][0]}
ratios = {k: (xt[k] * kinv(om[k])) % Rr for k in om} if set(xt) == set(om) else {}
check(len(ratios) == 3 and len({str(r) for r in ratios.values()}) == 1,
      "C2 the weight-0 row without new unknowns (x^19 y^38) is a K5-multiple of Omega", len(ratios) == 3)
def modp(a, p, w0):
    s = 0
    for i in range(a.degree() + 1):
        q_ = Fraction(int(a[i].p), int(a[i].q)); assert q_.denominator % p
        s = (s + q_.numerator * pow(q_.denominator, -1, p) * pow(w0, i, p)) % p
    return s
NAMES = ["Psi", "Phi1", "Phi2", "Theta1", "Theta2", "Theta3"]
CH = ["b_11_20", "b_11_21", "a_6_13", "a_7_15", "b_10_21"]    # t, s, r, u, q
WANT = {32003: (11147, 2737, [12952, 31121, 12695, 13510, 428, 25110]),
        1000003: (806739, 993853, [762014, 374785, 255877, 471424, 29370, 7420])}
for p, (w0, kp_want, F_want) in WANT.items():
    check((w0**5 - w0**4 + 3*w0**3 + 3*w0**2 + 26) % p == 0, f"C3 R(w0) = 0 mod p (p = {p}, w0 = {w0})", True)
    kp = modp(kappa, p, w0)
    check(kp == kp_want, f"C3 kappa mod {p}", kp)
    vals, nterms, wts = [], [], []
    for n in NAMES:
        # chart: b_12_22 = 1, b_12_23 = kappa; collect K5 terms in (t,s,r,u,q), then evaluate at (1,2,3,4,5) mod p
        terms = {}
        for m, c in conds[n]:
            mm = {}
            for v, e in m: mm[v] = mm.get(v, 0) + e
            coef = kpoly(c)
            for _ in range(mm.pop("b_12_23", 0)): coef = (coef * kappa) % Rr
            mm.pop("b_12_22", None)
            key = tuple(mm.get(v, 0) for v in CH)
            terms[key] = ((terms.get(key, fmpq_poly([0])) + coef) % Rr)
        terms = {k: v for k, v in terms.items() if v != 0}
        nterms.append(len(terms))
        wts.append(max(a + 2*b + 3*c_ + 3*d + 4*e for a, b, c_, d, e in terms))
        val = sum(modp(v, p, w0) * pow(1, k[0], p) * pow(2, k[1], p) * pow(3, k[2], p) * pow(4, k[3], p) * pow(5, k[4], p)
                  for k, v in terms.items()) % p
        vals.append(val)
    check(nterms == [22, 35, 35, 52, 52, 52], f"C3 nonzero K5 terms of the six chart generators", nterms)
    check(wts == [5, 6, 6, 7, 7, 7], f"C3 weighted degrees (t,s,r,u,q weights 1,2,3,3,4)", wts)
    check(vals == F_want, f"C3 F_n(1,2,3,4,5) mod {p} (Psi, Phi1, Phi2, Theta1, Theta2, Theta3)", vals)
print(f"ANSWER KEY CHECKS: {ok[0]} passed, {ok[1]} failed")
sys.exit(1 if ok[1] else 0)
