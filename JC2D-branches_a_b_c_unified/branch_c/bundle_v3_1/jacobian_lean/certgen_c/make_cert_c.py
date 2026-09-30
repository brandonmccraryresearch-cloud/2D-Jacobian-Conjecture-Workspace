"""
make_cert_c.py -- exact K5 certificate data for the branch-(c) layers E2 (with A_{-1}) and E1,
continuing the branch-(a,b) certificates (certgen/cert.json: top layer, E4 and E3 facts).

Branch (c): N(P) = conv{(0,0),(1,0),(8,14),(8,16),(0,8)}, N(Q) = conv{(0,0),(2,1),(12,21),(12,24),(0,12)}
(GGHV Prop. 4.3(1)).  The weight -4, -3, -2 bracket equations (E5, E4, E3) of branch (c) are
literally the branch-(a,b) ones (checked below), so the (a,b) E4/E3 certificates apply verbatim.

Weights (j - 2i of the bracket monomial x^i y^j):  E2 = -1, E1 = 0.
Unknowns:  E2:  Y = B0 (b_i_{2i}, i=1..12) + A_{-1} (a_i_{2i+1}, i=0..7)    [pipeline order]
           E1:  V = A_{-2} (a_i_{2i+2}, i=0..6) + B_{-1} (b_i_{2i+1}, i=0..11) [pipeline order]
Everything is exact over K5 = Q[w]/(R), R = w^5 - w^4 + 3w^3 + 3w^2 + 26, and every identity is
re-verified before being written to cert_c.json.
"""
import json, os, sys
from flint import fmpq_poly, fmpq
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "certgen"))
from gen_system import build

Rr = fmpq_poly([26, 0, 3, 3, -1, 1])
ZERO = fmpq_poly([0]); ONE = fmpq_poly([1])
def Kc(c): return fmpq_poly([fmpq(*map(int, s.split('/'))) if '/' in s else fmpq(int(s)) for s in c]) % Rr
def red(a): return a % Rr
def inv(a):
    g, s, _ = a.xgcd(Rr); assert g == 1; return s % Rr
def kstr(a): return [str(a[i]) for i in range(5)]

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
    out = {}
    for m, v in p.items():
        x = red(v * c)
        if x != 0: out[m] = x
    return out
def P_subst(p, sub):
    r = {}
    for m, c in p.items():
        t = P_const(c)
        for v, e in m:
            base = sub.get(v, P_var(v))
            for _ in range(e): t = P_mul(t, base)
        r = P_add(r, t)
    return r
def P_vars(p): return {v for m in p for v, _ in m}
def from_pj(pj): return {tuple((v, e) for v, e in m): Kc(c) for m, c in pj}
def pj(p): return [[[list(mm) for mm in m], kstr(c)] for m, c in p.items()]

cert = json.load(open(os.path.join(HERE, "..", "certgen", "cert.json")))
top = {v: Kc(c) for v, c in cert["top"].items()}
T1, T2, S1, S2 = cert["T1"], cert["T2"], cert["S1"], cert["S2"]
Z_, X_ = cert["Z"], cert["X"]
zsub = {v: from_pj(val) for v, val, _ in cert["E4"]}
xsub = {v: from_pj(val) for v, val, _ in cert["E3"]}
assert all(P_vars(p) <= {T1, T2} for p in zsub.values())
assert all(P_vars(p) <= {T1, T2, S1, S2} for p in xsub.values())

# ------------------------------------------------------------ branch-(c) bracket equations
NPc = [(0, 0), (1, 0), (8, 14), (8, 16), (0, 8)]
NQc = [(0, 0), (2, 1), (12, 21), (12, 24), (0, 12)]
LPc, LQc, eqsc, tgtc = build(NPc, NQc)
assert len(LPc) == 61 and len(LQc) == 125
wt = lambda ij: ij[1] - 2 * ij[0]
# E5, E4, E3 of branch (c) coincide with branch (a,b)
LPab, LQab, eqsab, _ = build()
for W in (-4, -3, -2):
    kc = sorted(k for k in eqsc if wt(k) == W); kab = sorted(k for k in eqsab if wt(k) == W)
    assert kc == kab, W
    for k in kc: assert sorted(eqsc[k]) == sorted(eqsab[k]), (W, k)
for W, tag in ((-3, "-3"), (-2, "-2")):
    assert [[list(k), [list(t) for t in eqsc[k]]] for k in sorted(k for k in eqsc if wt(k) == W)] == \
        [[list(k), [list(t) for t in T]] for k, T in cert["eqs"][tag]], W
print("E5/E4/E3 of branch (c) = branch (a,b): OK")
# the (a,b) top layer solves E5 with lam = 1
def eq_raw(k): return eqsc[k]
for k in sorted(k for k in eqsc if wt(k) == -4):
    s = ZERO
    for c, pv, qv in eqsc[k]:
        s = red(s + c * top.get(pv, ZERO) * top.get(qv, ZERO))
    assert s == (ONE if k == (2, 0) else ZERO), k
print("E5 at the rescaled K5 top layer: [P,Q]_top = x^2 (lam = 1): OK")

def eq_poly(k):
    p = {}
    for c, pv, qv in eqsc[k]:
        f = P_const(fmpq_poly([c]))
        for v in (pv, qv):
            f = P_mul(f, P_const(top[v]) if v in top else P_var(v))
        p = P_add(p, f)
    return p
def linrow(p, vars_):
    row = [ZERO] * len(vars_); idx = {v: i for i, v in enumerate(vars_)}
    for m, c in p.items():
        if len(m) == 1 and m[0][1] == 1 and m[0][0] in idx: row[idx[m[0][0]]] = c
    return row
def rref_with_transform(M, ncols):
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
def split_lin(ps, vars_):
    """p = M.vars + K with K free of vars_; returns (M rows, K polys)"""
    M = [linrow(p, vars_) for p in ps]
    K = [P_add(p, {((vars_[i], 1),): row[i] for i in range(len(vars_)) if row[i] != 0}, -1) for p, row in zip(ps, M)]
    for k in K: assert not (P_vars(k) & set(vars_)), "nonlinear in the layer unknowns"
    return M, K

blocks = {W: sorted(k for k in eqsc if wt(k) == W) for W in (-1, 0, 1, 2, 3)}
Y_ = [f"b_{i}_{2*i}" for i in range(1, 13)] + [f"a_{i}_{2*i+1}" for i in range(0, 8)]
V_ = [f"a_{i}_{2*i+2}" for i in range(0, 7)] + [f"b_{i}_{2*i+1}" for i in range(0, 12)]

# ------------------------------------------------------------ E2 (branch c)
sub_zx = dict(zsub); sub_zx.update(xsub)
E2raw = [eq_poly(k) for k in blocks[-1]]
E2s = [P_subst(p, sub_zx) for p in E2raw]
allvars2 = set().union(*[P_vars(p) for p in E2s])
assert allvars2 <= set(Y_) | {T1, T2, S1, S2}, allvars2 - set(Y_)
M2, K2 = split_lin(E2s, Y_)
A2, piv2, null2 = rref_with_transform(M2, len(Y_))
free2 = [c for c in range(len(Y_)) if c not in piv2]
print(f"E2(c): {len(M2)}x{len(Y_)}, rank {len(piv2)}, free {[Y_[c] for c in free2]}, left nullity {len(null2)}")
R1, R2 = Y_[free2[0]], Y_[free2[1]]
for nv in null2:            # compatibility: the left null vector kills K2 identically
    k = {}
    for ee, kk in zip(nv, K2): k = P_add(k, P_scale(kk, ee))
    assert k == {}, "E2(c) compatibility is NOT automatic"
print("E2(c) left-null vector kills the RHS identically (no condition at E2)")
ysub = {}; E2cert = []
for row, pc in zip(A2, piv2):
    Rw, Ew = row[:len(Y_)], row[len(Y_):]
    val = {}
    for f in free2:
        if Rw[f] != 0: val = P_add(val, {((Y_[f], 1),): red(-Rw[f])})
    for ee, kk in zip(Ew, K2): val = P_add(val, P_scale(kk, red(-ee)))
    ysub[Y_[pc]] = val
    lhs = P_add(P_var(Y_[pc]), val, -1); rhs = {}
    for ee, pe in zip(Ew, E2s): rhs = P_add(rhs, P_scale(pe, ee))
    assert P_add(lhs, rhs, -1) == {}
    E2cert.append((Y_[pc], val, Ew))
assert all(P_vars(p) <= {T1, T2, S1, S2, R1, R2} for p in ysub.values())

# ------------------------------------------------------------ E1
sub_zxy = dict(sub_zx); sub_zxy.update(ysub)
E1raw = [eq_poly(k) for k in blocks[0]]
E1s = [P_subst(p, sub_zxy) for p in E1raw]
allvars1 = set().union(*[P_vars(p) for p in E1s])
assert allvars1 <= set(V_) | {T1, T2, S1, S2, R1, R2}, allvars1 - set(V_)
M1, K1 = split_lin(E1s, V_)
zero_rows1 = [i for i, row in enumerate(M1) if all(x == 0 for x in row)]
print("E1 rows with no unknowns (pure conditions):", [blocks[0][i] for i in zero_rows1])
op_rows1 = [i for i in range(len(M1)) if i not in zero_rows1]
M1op = [M1[i] for i in op_rows1]
A1, piv1, null1 = rref_with_transform(M1op, len(V_))
free1 = [c for c in range(len(V_)) if c not in piv1]
print(f"E1 operator (pipeline rows): {len(M1op)}x{len(V_)}, rank {len(piv1)}, free {[V_[c] for c in free1]}, left nullity {len(null1)}")
assert len(null1) == 1
W1 = [ZERO] * len(M1)
for j, i in enumerate(op_rows1): W1[i] = null1[0][j]
Om = {}
for ee, pe in zip(W1, E1s): Om = P_add(Om, P_scale(pe, ee))
print("Omega monomials:", sorted(Om.keys()))
assert P_vars(Om) <= {T2, S2}
Xtra1 = [E1s[i] for i in zero_rows1]
for i, p in zip(zero_rows1, Xtra1):
    print("extra E1 condition at", blocks[0][i], ":", len(p), "terms; vars", sorted(P_vars(p)))
# normalise: coefficient of s2^2 := 1 ?  keep raw, and also report ratios
def digits(a): return max(len(str(a[i].p)) + len(str(a[i].q)) for i in range(5))
for m, c in Om.items(): print("  ", m, "digits", digits(c))

# compare with the pipeline coefficients c1,c2,c3 (a2_2 = 1 normalisation) via e^10 scalings
e = Kc(cert["e"])
pipe = json.load(open(os.path.join(HERE, "omega_pipeline.json")))
c1, c2, c3 = (Kc(pipe[k]) for k in ("c1", "c2", "c3"))
o1 = Om.get(((S2, 2),), ZERO); o2 = Om.get(tuple(sorted(((T2, 2), (S2, 1)))), ZERO); o3 = Om.get(((T2, 4),), ZERO)
rho = red(o1 * inv(red(c1 * e ** 20)))
print("o1 = rho*c1*e^20 by definition; check o2 = rho*c2*e^10:", red(o2 - rho * c2 * e ** 10) == 0,
      "; o3 = rho*c3:", red(o3 - rho * c3) == 0)
json.dump(dict(R1=R1, R2=R2, Y=Y_, V=V_, Qv=V_[free1[0]],
               eqs={str(W): [[list(k), [list(t) for t in eqsc[k]]] for k in blocks[W]] for W in (-1, 0, 1, 2, 3)},
               E2=[[v, pj(val), [kstr(x) for x in E_]] for v, val, E_ in E2cert],
               E2red=[pj(p) for p in E2s], E1red=[pj(p) for p in E1s], W1=[kstr(x) for x in W1], E1zero=zero_rows1, Xtra1=[pj(p) for p in Xtra1],
               Omega=pj(Om), rho=kstr(rho)),
          open(os.path.join(HERE, "cert_c.json"), "w"))
print("max digits  ysub:", max(max(digits(c) for c in p.values()) for p in ysub.values()),
      " E2 mult:", max(digits(x) for _, _, E_ in E2cert for x in E_ if x != 0),
      " W1:", max(digits(x) for x in W1 if x != 0), " E1red:", max(max(digits(c) for c in p.values()) for p in E1s))
print("wrote cert_c.json")
