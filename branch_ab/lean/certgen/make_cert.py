"""
make_cert.py -- exact certificate data for the E4 -> E3 -> E2 -> minors descent at the rescaled
K5 top-layer point.  Everything is exact over K5 = Q[w]/(R), R = w^5 - w^4 + 3w^3 + 3w^2 + 26.

The top layer is the point of e5_exact_K5.json (normalisation a_1_0 = b_2_1 = a_2_2 = 1) rescaled
by the torus element e (a_{i,2i-2} -> e^(i-1) a, b_{k,2k-3} -> e^(k-2) b), which keeps
a_1_0 = b_2_1 = 1 and reduces heights ~10x.

Produces cert.json with:
  top      : top-layer values (K5 elements, coefficient lists low->high in w)
  eqs      : scalar bracket equations of weights -3, -2, -1  (lists of (int c, pvar, qvar))
  E4, E3   : RREF certificates   z_p = lin(t)  /  x_p = quad(t) + lin(s)
  W, F     : E2 left-null combinations and the 7 conditions F_i = b_i + s1 M_i + s2 L_i
  G0, G1   : multipliers with t1^5 = sum_r G0_r F_r and t2^5 = sum_r G1_r F_r
  inv12    : multipliers with b_12_24 = sum_e inv12_e * eq2_e  at t = 0
Every identity is re-verified exactly before writing.
"""
import json, os, sys, itertools
from fractions import Fraction
from flint import fmpq_poly, fmpq
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_system import build

Rr = fmpq_poly([26, 0, 3, 3, -1, 1])
ZERO = fmpq_poly([0]); ONE = fmpq_poly([1])
def Kc(c): return fmpq_poly([fmpq(*map(int, s.split('/'))) if '/' in s else fmpq(int(s)) for s in c]) % Rr
def red(a): return a % Rr
def inv(a):
    g, s, _ = a.xgcd(Rr); assert g == 1; return s % Rr
def kstr(a):
    return [str(a[i]) for i in range(5)]

# ---------------------------------------------------------------- sparse polynomials over K5
# monomial = tuple of sorted (var, exp) pairs; poly = dict monomial -> K5 element (nonzero)
def P_const(c): return {(): red(c)} if red(c) != 0 else {}
def P_var(v): return {((v, 1),): ONE}
def P_add(p, q, s=1):
    r = dict(p)
    for m, c in q.items():
        x = red(r.get(m, ZERO) + (c if s == 1 else -c))
        if x != 0: r[m] = x
        elif m in r: del r[m]
    return r
def mono_mul(m1, m2):
    d = dict(m1)
    for v, e in m2: d[v] = d.get(v, 0) + e
    return tuple(sorted(d.items()))
def P_mul(p, q):
    r = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = mono_mul(m1, m2); x = red(r.get(m, ZERO) + c1 * c2)
            if x != 0: r[m] = x
            elif m in r: del r[m]
    return r
def P_scale(p, c):
    return {m: red(v * c) for m, v in p.items() if red(v * c) != 0}
def P_subst(p, sub):
    """substitute variables by polynomials"""
    r = {}
    for m, c in p.items():
        t = P_const(c)
        for v, e in m:
            base = sub.get(v, P_var(v))
            for _ in range(e): t = P_mul(t, base)
        r = P_add(r, t)
    return r

# ---------------------------------------------------------------- top layer, rescaled
d = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "e5_exact_K5.json")))
top0 = {v: Kc(c) for v, c in d.items() if not v.startswith("_")}
top0.update({"a_1_0": ONE, "b_2_1": ONE, "a_2_2": ONE})
e = red(fmpq_poly([fmpq(303, 16), fmpq(879, 128), fmpq(-389, 128), fmpq(-51, 128), fmpq(49, 128)]))
def texp(v):
    i = int(v.split('_')[1]); return i - 1 if v[0] == 'a' else i - 2
top = {}
for v, x in top0.items():
    if v == 'lam': continue
    top[v] = red(x * e ** texp(v))
assert top["a_1_0"] == ONE and top["b_2_1"] == ONE

# ---------------------------------------------------------------- equations
LP, LQ, eqs, tgt = build()
wt = lambda ij: ij[1] - 2 * ij[0]
vw = lambda v: wt(tuple(map(int, v.split('_')[1:])))
key = lambda v: (v[0], int(v.split('_')[1]), int(v.split('_')[2]))
allv = sorted({v for T in eqs.values() for c, pv, qv in T for v in (pv, qv)}, key=key)
TOPV = sorted(top, key=key)
Z_ = [v for v in allv if (v[0] == 'a' and vw(v) == -1) or (v[0] == 'b' and vw(v) == -2)]
X_ = [v for v in allv if (v[0] == 'a' and vw(v) == 0 and v != 'a_0_0') or (v[0] == 'b' and vw(v) == -1)]
B0_ = [v for v in allv if v[0] == 'b' and vw(v) == 0 and v != 'b_0_0']
assert set(TOPV) == {v for v in allv if (v[0] == 'a' and vw(v) == -2) or (v[0] == 'b' and vw(v) == -3)}
blocks = {W: [k for k in sorted(eqs) if wt(k) == W] for W in (-3, -2, -1)}
def eq_poly(k):
    """equation polynomial with top-layer values substituted"""
    p = {}
    for c, pv, qv in eqs[k]:
        f = P_const(fmpq_poly([c]))
        for v in (pv, qv):
            f = P_mul(f, P_const(top[v]) if v in top else P_var(v))
        p = P_add(p, f)
    return p
E4eq = [eq_poly(k) for k in blocks[-3]]
E3eq = [eq_poly(k) for k in blocks[-2]]
E2eq = [eq_poly(k) for k in blocks[-1]]
print("equations:", len(E4eq), len(E3eq), len(E2eq), " unknowns:", len(Z_), len(X_), len(B0_))

def linrow(p, vars_):
    """coefficients of the part of p that is linear in vars_ (monomials of degree 1 in vars_ only)"""
    row = [ZERO] * len(vars_); idx = {v: i for i, v in enumerate(vars_)}
    for m, c in p.items():
        if len(m) == 1 and m[0][1] == 1 and m[0][0] in idx:
            row[idx[m[0][0]]] = c
    return row

def rref_with_transform(M, ncols):
    """Gauss-Jordan on [M | I]; returns (rows of [R | E] for pivot rows, pivot cols, left-null rows)"""
    m = len(M)
    A = [M[i][:] + [ONE if j == i else ZERO for j in range(m)] for i in range(m)]
    piv = []; r = 0
    for c in range(ncols):
        i = next((i for i in range(r, m) if A[i][c] != 0), None)
        if i is None: continue
        A[r], A[i] = A[i], A[r]
        iv = inv(A[r][c]); A[r] = [red(x * iv) for x in A[r]]
        for j in range(m):
            if j != r and A[j][c] != 0:
                f = A[j][c]; A[j] = [red(A[j][l] - f * A[r][l]) for l in range(len(A[r]))]
        piv.append(c); r += 1
    return A[:r], piv, [row[ncols:] for row in A[r:]]

# ---------------------------------------------------------------- E4
M4 = [linrow(p, Z_) for p in E4eq]
for p, row in zip(E4eq, M4):    # E4 is exactly linear homogeneous in Z_
    assert P_add(p, {((Z_[i], 1),): row[i] for i in range(len(Z_)) if row[i] != 0}, -1) == {}
A4, piv4, null4 = rref_with_transform(M4, len(Z_))
free4 = [c for c in range(len(Z_)) if c not in piv4]
print("E4 rank", len(piv4), "free", [Z_[c] for c in free4])
T1, T2 = Z_[free4[0]], Z_[free4[1]]
zsub = {}          # pivot z -> polynomial in t
E4cert = []
for row, pc in zip(A4, piv4):
    R_, E_ = row[:len(Z_)], row[len(Z_):]
    val = {}
    for f in free4:
        if R_[f] != 0: val = P_add(val, {((Z_[f], 1),): red(-R_[f])})
    zsub[Z_[pc]] = val
    # identity: z_p - val = sum_e E_e * eq_e
    lhs = P_add(P_var(Z_[pc]), val, -1)
    rhs = {}
    for ee, pe in zip(E_, E4eq): rhs = P_add(rhs, P_scale(pe, ee))
    assert P_add(lhs, rhs, -1) == {}
    E4cert.append((Z_[pc], val, E_))

# ---------------------------------------------------------------- E3
E3s = [P_subst(p, zsub) for p in E3eq]
M3 = [linrow(p, X_) for p in E3s]
Kq = [P_add(p, {((X_[i], 1),): row[i] for i in range(len(X_)) if row[i] != 0}, -1) for p, row in zip(E3s, M3)]
assert all(all(v in (T1, T2) for m in k for v, _ in m) for k in Kq)
A3, piv3, null3 = rref_with_transform(M3, len(X_))
free3 = [c for c in range(len(X_)) if c not in piv3]
print("E3 rank", len(piv3), "free", [X_[c] for c in free3])
S1, S2 = X_[free3[0]], X_[free3[1]]
# consistency (left null vector kills K) -- needed for solvability, not for the obstruction
for nv in null3:
    k = {}
    for ee, kk in zip(nv, Kq): k = P_add(k, P_scale(kk, ee))
    assert k == {}, "E3 inconsistent"
xsub = {}; E3cert = []
for row, pc in zip(A3, piv3):
    R_, E_ = row[:len(X_)], row[len(X_):]
    val = {}
    for f in free3:
        if R_[f] != 0: val = P_add(val, {((X_[f], 1),): red(-R_[f])})
    for ee, kk in zip(E_, Kq): val = P_add(val, P_scale(kk, red(-ee)))
    xsub[X_[pc]] = val
    lhs = P_add(P_var(X_[pc]), val, -1)
    rhs = {}
    for ee, pe in zip(E_, E3s): rhs = P_add(rhs, P_scale(pe, ee))
    assert P_add(lhs, rhs, -1) == {}
    E3cert.append((X_[pc], val, E_))

# ---------------------------------------------------------------- E2
E2s = [P_subst(P_subst(p, zsub), xsub) for p in E2eq]
M2 = [linrow(p, B0_) for p in E2s]
A2, piv2, W = rref_with_transform(M2, len(B0_))
print("E2 rank", len(piv2), "left nullity", len(W))
Fs = []
for wrow in W:
    f = {}
    for ee, pe in zip(wrow, E2s): f = P_add(f, P_scale(pe, ee))
    assert all(v in (T1, T2, S1, S2) for m in f for v, _ in m), "B0 did not cancel"
    Fs.append(f)
# F_i = b_i(t) + s1 M_i(t) + s2 L_i(t)
def split(f):
    b, M, L = {}, {}, {}
    for m, c in f.items():
        dm = dict(m)
        if S1 in dm: M[tuple((v, e) for v, e in m if v != S1)] = c; assert dm[S1] == 1 and S2 not in dm
        elif S2 in dm: L[tuple((v, e) for v, e in m if v != S2)] = c; assert dm[S2] == 1
        else: b[m] = c
    return b, M, L
bML = [split(f) for f in Fs]
for b, M, L in bML:
    assert all(sum(e for _, e in m) == 3 for m in b) and all(sum(e for _, e in m) == 1 for m in M) \
        and all(sum(e for _, e in m) == 1 for m in L)

# ---------------------------------------------------------------- minors and span certificate
def det3(r0, r1, r2):
    (a, b, c), (d_, e_, f), (g, h, i) = r0, r1, r2
    t1 = P_mul(a, P_add(P_mul(e_, i), P_mul(f, h), -1))
    t2 = P_mul(b, P_add(P_mul(d_, i), P_mul(f, g), -1))
    t3 = P_mul(c, P_add(P_mul(d_, h), P_mul(e_, g), -1))
    return P_add(P_add(t1, t2, -1), t3)
triples = list(itertools.combinations(range(7), 3))
minors = [det3(*[bML[r] for r in tr]) for tr in triples]
quint = [((T1, 5 - j), (T2, j)) if 0 < j < 5 else (((T1, 5),) if j == 0 else ((T2, 5),)) for j in range(6)]
quint = [tuple(sorted(q)) for q in quint]
for m in minors: assert all(k in quint for k in m)
Cm = [[mm.get(q, ZERO) for q in quint] for mm in minors]
print("nonzero minors:", sum(any(x != 0 for x in r) for r in Cm), " rank:", len(rref_with_transform(Cm, 6)[1]))
# solve c^T Cm = unit vector for t1^5 (index 0) and t2^5 (index 5): pick 6 independent minors
_, pivrows, _ = rref_with_transform([list(col) for col in zip(*Cm)], len(Cm))   # pivots = independent rows of Cm
sel = pivrows[:6]
S6 = [Cm[r] for r in sel]                       # 6x6, rows = selected minors
# want coefficients c (len 6) with sum_r c_r S6[r] = e_j  -> S6^T c = e_j
def solve(Mt, rhs):
    n = len(Mt)
    A = [Mt[i][:] + [rhs[i]] for i in range(n)]
    for c in range(n):
        i = next(i for i in range(c, n) if A[i][c] != 0)
        A[c], A[i] = A[i], A[c]; iv = inv(A[c][c]); A[c] = [red(x * iv) for x in A[c]]
        for j in range(n):
            if j != c and A[j][c] != 0:
                f = A[j][c]; A[j] = [red(A[j][l] - f * A[c][l]) for l in range(n + 1)]
    return [A[i][n] for i in range(n)]
S6T = [list(col) for col in zip(*S6)]
c0 = solve(S6T, [ONE if j == 0 else ZERO for j in range(6)])
c1 = solve(S6T, [ONE if j == 5 else ZERO for j in range(6)])
for cc, target in ((c0, quint[0]), (c1, quint[5])):
    tot = {}
    for r, ci in zip(sel, cc): tot = P_add(tot, P_scale(minors[r], ci))
    assert tot == {target: ONE}
# G multipliers: det[b|M|L]_{ijk} = sum_{r in ijk} F_r * cof_r  (cofactor of first column)
def cof(tr):
    i, j, k = tr
    Mi, Li = bML[i][1], bML[i][2]; Mj, Lj = bML[j][1], bML[j][2]; Mk, Lk = bML[k][1], bML[k][2]
    return {i: P_add(P_mul(Mj, Lk), P_mul(Mk, Lj), -1),
            j: P_scale(P_add(P_mul(Mi, Lk), P_mul(Mk, Li), -1), fmpq_poly([-1])),
            k: P_add(P_mul(Mi, Lj), P_mul(Mj, Li), -1)}
def Gmult(cc):
    G = [dict() for _ in range(7)]
    for r, ci in zip(sel, cc):
        for row, cf in cof(triples[r]).items():
            G[row] = P_add(G[row], P_scale(cf, ci))
    return G
G0m, G1m = Gmult(c0), Gmult(c1)          # minor-based multipliers (kept for the PARI cross-check)
# smaller multipliers: solve sum_r G_r F_r = target directly (G_r quadratic in t), random pivot orders
import random
Tm = [((T1, 2),), tuple(sorted(((T1, 1), (T2, 1)))), ((T2, 2),)]
unk = [(r, m) for r in range(7) for m in Tm]
prods = [P_mul({m: ONE}, Fs[r]) for r, m in unk]
monos = sorted({mm for p in prods for mm in p})
Mt = [[p.get(mm, ZERO) for p in prods] for mm in monos]
def kd(a): return max(len(str(a[i].p)) + len(str(a[i].q)) for i in range(5))
def solve_order(order, target):
    A = [[row[c] for c in order] + [ONE if mm == target else ZERO] for row, mm in zip(Mt, monos)]
    n = len(order); piv = []; r = 0
    for c in range(n):
        i = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if i is None: continue
        A[r], A[i] = A[i], A[r]; iv = inv(A[r][c]); A[r] = [red(x * iv) for x in A[r]]
        for j in range(len(A)):
            if j != r and A[j][c] != 0:
                f = A[j][c]; A[j] = [red(A[j][l] - f * A[r][l]) for l in range(n + 1)]
        piv.append(c); r += 1
    assert all(A[i][n] == 0 for i in range(r, len(A)))
    sol = [ZERO] * len(unk)
    for i, c in enumerate(piv): sol[order[c]] = A[i][n]
    return sol
random.seed(1)
GG = []
for target in (quint[0], quint[5]):
    best = None
    for trial in range(int(sys.argv[1]) if len(sys.argv) > 1 else 150):
        order = list(range(len(unk))); random.shuffle(order)
        sol = solve_order(order, target); h = max(kd(x) for x in sol if x != 0)
        if best is None or h < best[0]: best = (h, sol)
    G = [dict() for _ in range(7)]
    for (r, m), x in zip(unk, best[1]):
        if x != 0: G[r] = P_add(G[r], {m: x})
    GG.append(G); print("direct G multipliers, max digits:", best[0])
G0, G1 = GG
for G, target in ((G0, quint[0]), (G1, quint[5]), (G0m, quint[0]), (G1m, quint[5])):
    tot = {}
    for g, f in zip(G, Fs): tot = P_add(tot, P_mul(g, f))
    assert tot == {target: ONE}, "span certificate failed"
print("span certificate: t1^5 and t2^5 verified as combinations of the 7 conditions")

# ---------------------------------------------------------------- t = 0: b_12_24 from E2
zero_t = {T1: {}, T2: {}}
E2t0 = [P_subst(p, zero_t) for p in E2s]
M2t0 = [linrow(p, B0_) for p in E2t0]
for p, row in zip(E2t0, M2t0):   # at t=0 the E2 equations are exactly M2 * B0 (s drops out)
    assert P_add(p, {((B0_[i], 1),): row[i] for i in range(len(B0_)) if row[i] != 0}, -1) == {}
Ar, pv, _ = rref_with_transform(M2t0, len(B0_))
tgt_col = B0_.index("b_12_24")
rowi = pv.index(tgt_col); inv12 = Ar[rowi][len(B0_):]
assert all(Ar[rowi][c] == (ONE if c == tgt_col else ZERO) for c in range(len(B0_)))
chk = {}
for ee, pe in zip(inv12, E2t0): chk = P_add(chk, P_scale(pe, ee))
assert chk == P_var("b_12_24")
print("t=0 certificate: b_12_24 = sum inv12_e * E2_e verified")

# ---------------------------------------------------------------- sizes and output
def pdig(p): return max((len(str(c[i].p)) + len(str(c[i].q)) for c in p.values() for i in range(5)), default=0)
def kdig(a): return max(len(str(a[i].p)) + len(str(a[i].q)) for i in range(5))
print("max digits  top:", max(kdig(v) for v in top.values()),
      " E4 mult:", max(kdig(x) for _, _, E_ in E4cert for x in E_),
      " E3 mult:", max(kdig(x) for _, _, E_ in E3cert for x in E_),
      " zsub:", max(pdig(v) for v in zsub.values()), " xsub:", max(pdig(v) for v in xsub.values()),
      " W:", max(kdig(x) for r in W for x in r), " F:", max(pdig(f) for f in Fs),
      " G:", max(pdig(g) for g in G0 + G1), " inv12:", max(kdig(x) for x in inv12))
def pj(p): return [[[list(mm) for mm in m], kstr(c)] for m, c in p.items()]
out = dict(R="w^5 - w^4 + 3*w^3 + 3*w^2 + 26", e=kstr(e), T1=T1, T2=T2, S1=S1, S2=S2,
           top={v: kstr(x) for v, x in top.items()}, Z=Z_, X=X_, B0=B0_,
           eqs={str(W_): [[k, eqs[k]] for k in blocks[W_]] for W_ in (-3, -2, -1)},
           E4=[[v, pj(val), [kstr(x) for x in E_]] for v, val, E_ in E4cert],
           E3=[[v, pj(val), [kstr(x) for x in E_]] for v, val, E_ in E3cert],
           W=[[kstr(x) for x in r] for r in W], F=[pj(f) for f in Fs], E3red=[pj(p) for p in E3s], E2red=[pj(p) for p in E2s],
           G0=[pj(g) for g in G0], G1=[pj(g) for g in G1], inv12=[kstr(x) for x in inv12],
           minors_sel=[list(triples[r]) for r in sel], bML=[[pj(b), pj(M), pj(L)] for b, M, L in bML], c0=[kstr(x) for x in c0], c1=[kstr(x) for x in c1])
json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "cert.json"), "w"))
print("wrote cert.json")
