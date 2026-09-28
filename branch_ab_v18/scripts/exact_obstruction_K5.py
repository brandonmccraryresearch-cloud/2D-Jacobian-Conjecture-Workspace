# Attribution: computed by the referee (Claude/Anthropic, Tier 1 agent) during Round 6 review.
# Part of the characteristic-0 verification for the branch-(a,b) elimination.

"""
exact_obstruction_K5.py -- the paper's E4 -> E3 -> E2 -> 35-minor obstruction, redone EXACTLY in
characteristic 0 over K5 (no reduction mod 101, no lifting lemma), at the exactly verified
top-layer point of e5_exact_K5.json.  Built from my own equation generator (gen_system.py).
Steps:
 1. E4 (weight -3): M4 (18x19) on t-variables (A1,B2); exact kernel {k1,k2}; (A1,B2) = t1 k1 + t2 k2.
 2. E3 (weight -2): M3 (19x20) on x = (A0,B1) plus bilinear part in (A1,B2).  Solve
    M3 x_ij = -K_ij for the monomials t1^2, t1 t2, t2^2 (consistency checked exactly),
    kernel {w1,w2}; x = t1^2 x11 + t1 t2 x12 + t2^2 x22 + s1 w1 + s2 w2.
 3. E2 (weight -1): M2 (19x12) on B0 plus bilinear part R(t,x).  Left null space W (7 x 19).
    Conditions  W.R = b_i(t) + s1 M_i(t) + s2 L_i(t),  i = 1..7   (exact over K5[t1,t2]).
 4. All 35 3x3 minors det[b|M|L] (binary quintics over K5); rank of their 35x6 coefficient
    matrix.  Rank 6  <=>  the minors span all binary quintics  =>  common zero only t = 0.
 5. Planted known-good control: shift the E2 inhomogeneity by a constant vector so
    that a planted (t0, s0, b0*) solves the E2 system, then confirm the steps-1-4
    machinery reports it consistent -- the 7 conditions vanish at (t0, s0), all 35
    minors vanish at t0, the 7x3 condition matrix drops from full rank 3 (original,
    obstructed at t0) to rank <= 2 (planted, consistent), and the planted E2 system
    is directly solvable with zero residual.  (The planted minors are inhomogeneous,
    so the homogeneous rank-6 span criterion is replaced by the condition-matrix
    rank comparison.)
 5b. Cubic planted control: subtract delta_i*(t1/t0_1)^3 from each b_i, keeping the
    conditions homogeneous cubic in t, so the 35 minors stay homogeneous quintics.
    The minor rank drops from 6 to 5, testing the final rank-6 step against a
    known-good case.
 6. End-to-end residual check (not tautological): plug numeric (t,s) into the
    constructed A1,B2,A0,B1 and evaluate the ORIGINAL weight -3 and -2 bracket
    equations directly from the generator; both must vanish exactly.  Then compare
    the E2 inhomogeneity R evaluated symbolically vs directly.
"""
import json, sys, itertools
from flint import fmpq_poly, fmpq
sys.path.insert(0, ".")
from gen_system import build

Rr = fmpq_poly([26, 0, 3, 3, -1, 1])
Z = fmpq_poly([0]); ONE = fmpq_poly([1])
def K(c):
    return fmpq_poly([fmpq(*map(int, s.split('/'))) if '/' in s else fmpq(int(s)) for s in c]) % Rr
def inv(a):
    g, s, _ = a.xgcd(Rr); assert g == 1; return s % Rr
d = json.load(open("e5_exact_K5.json"))
top = {v: K(c) for v, c in d.items() if not v.startswith("_")}
top.update({"a_1_0": ONE, "b_2_1": ONE, "a_2_2": ONE})

LP, LQ, eqs, tgt = build()
w_ = lambda ij: ij[1] - 2 * ij[0]
vw = lambda v: w_(tuple(map(int, v.split('_')[1:])))
key = lambda v: (v[0], int(v.split('_')[1]), int(v.split('_')[2]))
allv = sorted({v for T in eqs.values() for c, pv, qv in T for v in (pv, qv)}, key=key)
T_ = [v for v in allv if (v[0] == 'a' and vw(v) == -1) or (v[0] == 'b' and vw(v) == -2)]            # A1,B2
X_ = [v for v in allv if (v[0] == 'a' and vw(v) == 0 and v != 'a_0_0') or (v[0] == 'b' and vw(v) == -1)]  # A0,B1
B0_ = [v for v in allv if v[0] == 'b' and vw(v) == 0 and v != 'b_0_0']
blocks = {W: [k for k in sorted(eqs) if w_(k) == W] for W in (-3, -2, -1)}

# ---------- exact linear algebra over K5
def rref(M, ncols):
    M = [r[:] for r in M]; piv = []; r = 0
    for c in range(ncols):
        i = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if i is None: continue
        M[r], M[i] = M[i], M[r]
        iv = inv(M[r][c]); M[r] = [(x * iv) % Rr for x in M[r]]
        for j in range(len(M)):
            if j != r and M[j][c] != 0:
                f = M[j][c]; M[j] = [(M[j][l] - f * M[r][l]) % Rr for l in range(len(M[r]))]
        piv.append(c); r += 1
    return M, piv
def kernel(M, n):
    R_, piv = rref(M, n)
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        v = [Z] * n; v[f] = ONE
        for i, pc in enumerate(piv): v[pc] = (-R_[i][f]) % Rr
        basis.append(v)
    return basis, len(piv)
def solve(M, b, n):
    A = [M[i] + [b[i]] for i in range(len(M))]
    R_, piv = rref(A, n)
    if n in piv: return None
    x = [Z] * n
    for i, pc in enumerate(piv): x[pc] = R_[i][n]
    return x
def matvec(M, x):
    return [sum((M[i][j] * x[j] for j in range(len(x))), Z) % Rr for i in range(len(M))]

# ---------- binary forms in (t1,t2) (and s1,s2) over K5 : dict {(e1,e2,f1,f2): K5}
def padd(a, b):
    c = dict(a)
    for k, v in b.items():
        c[k] = (c.get(k, Z) + v) % Rr
    return {k: v for k, v in c.items() if v != 0}
def pmul(a, b):
    c = {}
    for k1, v1 in a.items():
        for k2, v2 in b.items():
            k = tuple(x + y for x, y in zip(k1, k2)); c[k] = (c.get(k, Z) + v1 * v2) % Rr
    return {k: v for k, v in c.items() if v != 0}
def pscale(a, s):
    return {k: (v * s) % Rr for k, v in a.items() if (v * s) % Rr != 0}
T1 = {(1, 0, 0, 0): ONE}; T2 = {(0, 1, 0, 0): ONE}; S1 = {(0, 0, 1, 0): ONE}; S2 = {(0, 0, 0, 1): ONE}
T11 = pmul(T1, T1); T12 = pmul(T1, T2); T22 = pmul(T2, T2)

def lin_matrix(W, U, env):
    """rows = equations of weight W; columns = unknowns U; coefficient from product with a variable in env (constants)."""
    idx = {u: i for i, u in enumerate(U)}; rows = []
    for k in blocks[W]:
        row = [Z] * len(U)
        for c, pv, qv in eqs[k]:
            for a, b in ((pv, qv), (qv, pv)):
                if a in idx and b in env:
                    row[idx[a]] = (row[idx[a]] + c * env[b]) % Rr
        rows.append(row)
    return rows
def bilinear_part(W, val):
    """for equations of weight W: sum of c*val[p]*val[q] over terms where both p,q are in val (polynomial values)."""
    out = []
    for k in blocks[W]:
        acc = {}
        for c, pv, qv in eqs[k]:
            if pv in val and qv in val:
                acc = padd(acc, pscale(pmul(val[pv], val[qv]), fmpq_poly([c])))
        out.append(acc)
    return out

# 1. E4
M4 = lin_matrix(-3, T_, top)
kb4, r4 = kernel(M4, len(T_))
assert all(all(x == 0 for x in matvec(M4, v)) for v in kb4)
print(f"E4: {len(M4)}x{len(T_)}, rank {r4}, kernel {len(kb4)} (exact, char 0); kernel residuals zero")
assert len(kb4) == 2
tval = {u: padd(pscale(T1, kb4[0][i]), pscale(T2, kb4[1][i])) for i, u in enumerate(T_)}

# 2. E3
M3 = lin_matrix(-2, X_, top)
Kt = bilinear_part(-2, tval)                       # inhomogeneous part, quadratic in t
def coeff_vec(polys, mono):
    return [p_.get(mono, Z) for p_ in polys]
kb3, r3 = kernel(M3, len(X_))
print(f"E3: {len(M3)}x{len(X_)}, rank {r3}, kernel {len(kb3)}")
xs = {}
for name, mono in (("11", (2, 0, 0, 0)), ("12", (1, 1, 0, 0)), ("22", (0, 2, 0, 0))):
    rhs = [(-c) % Rr for c in coeff_vec(Kt, mono)]           # M3 x = -K  (E3: M3 x + K = 0)
    x = solve(M3, rhs, len(X_))
    assert x is not None, f"E3 inconsistent for t-monomial {name} in characteristic 0"
    assert all(((a + b) % Rr) == 0 for a, b in zip(matvec(M3, x), coeff_vec(Kt, mono)))
    xs[name] = x
print("E3 solvable for every t in characteristic 0 (consistency of all three t-monomials checked exactly); residuals M3 x + K = 0")
xval = {}
for i, u in enumerate(X_):
    pol = {}
    for name, T_mono in (("11", T11), ("12", T12), ("22", T22)):
        pol = padd(pol, pscale(T_mono, xs[name][i]))
    pol = padd(pol, pscale(S1, kb3[0][i])); pol = padd(pol, pscale(S2, kb3[1][i]))
    xval[u] = pol

# 3. E2
M2 = lin_matrix(-1, B0_, top)
MT = [[M2[i][j] for i in range(len(M2))] for j in range(len(B0_))]
Wl, r2 = kernel(MT, len(M2))
print(f"E2: {len(M2)}x{len(B0_)}, rank {r2}, left nullity {len(Wl)}")
for wv in Wl:
    assert all(sum((wv[i] * M2[i][j] for i in range(len(M2))), Z) % Rr == 0 for j in range(len(B0_)))
val = dict(tval); val.update(xval)
Rt = bilinear_part(-1, val)                        # E2: M2 b0 + R = 0
conds = []
for wv in Wl:
    c = {}
    for i in range(len(M2)):
        c = padd(c, pscale(Rt[i], wv[i]))
    conds.append(c)
def split_s(c):
    b, m, l = {}, {}, {}
    for k, v in c.items():
        e1, e2, f1, f2 = k
        if f1 == 0 and f2 == 0: b[k] = v
        elif (f1, f2) == (1, 0): m[(e1, e2, 0, 0)] = v
        elif (f1, f2) == (0, 1): l[(e1, e2, 0, 0)] = v
        else: raise AssertionError("condition not affine-linear in s")
    return b, m, l
BML = [split_s(c) for c in conds]
assert all(all(k[0] + k[1] == 3 for k in b) and all(k[0] + k[1] == 1 for k in m) and all(k[0] + k[1] == 1 for k in l) for b, m, l in BML)
print("7 conditions: b_i cubic, M_i and L_i linear in t (exact) -- matches the paper's Lemma 8.2 shape")

# 4. minors
def det3(rows):
    (a, b, c), (d_, e, f), (g, h, i) = rows
    t1_ = pmul(a, padd(pmul(e, i), pscale(pmul(f, h), -ONE)))
    t2_ = pmul(b, padd(pmul(d_, i), pscale(pmul(f, g), -ONE)))
    t3_ = pmul(c, padd(pmul(d_, h), pscale(pmul(e, g), -ONE)))
    return padd(padd(t1_, pscale(t2_, -ONE)), t3_)
minors = [det3([BML[i], BML[j], BML[k]]) for i, j, k in itertools.combinations(range(7), 3)]
quint = [(5 - j, j, 0, 0) for j in range(6)]
assert all(all(k in quint for k in m) for m in minors)
C = [[m.get(q, Z) for q in quint] for m in minors]
_, rk = rref(C, 6)
print(f"35 minors: rank of 35x6 coefficient matrix over K5 = {len(rk)}  (6 means they span ALL binary quintics)")

# 5. planted KNOWN-GOOD control: shift the E2 inhomogeneity by a constant vector so
#    that a planted (t0, s0, b0*) solves the E2 system, then check the steps-1-4
#    machinery reports it consistent (conditions vanish, minors vanish at t0, minor
#    rank drops below 6, planted system directly solvable, and t0 was obstructed
#    before planting so the control is not vacuous).
def evalp(p_, t, s):
    acc = Z
    for (e1, e2, f1, f2), v in p_.items():
        acc = (acc + v * (fmpq(t[0]) ** e1) * (fmpq(t[1]) ** e2) * (fmpq(s[0]) ** f1) * (fmpq(s[1]) ** f2)) % Rr
    return acc
def eval_cond(bml, t, s):
    b, m, l = bml
    return ((evalp(b, t, (0, 0)) + fmpq(s[0]) * evalp(m, t, (0, 0))
             + fmpq(s[1]) * evalp(l, t, (0, 0)))) % Rr

pt0, ps0 = (4, 9), (2, 6)
b0star = [fmpq_poly([i + 1]) for i in range(len(B0_))]   # planted B0 solution
R_at = [evalp(r, pt0, ps0) for r in Rt]                  # R(t0, s0)
M2b0 = matvec(M2, b0star)
Cshift = [(-a - b) % Rr for a, b in zip(R_at, M2b0)]     # R(t0,s0) + C = -M2 b0*
Rtilde = [padd(r, {(0, 0, 0, 0): c}) for r, c in zip(Rt, Cshift)]
conds_p = []
for wv in Wl:
    c = {}
    for i in range(len(M2)):
        c = padd(c, pscale(Rtilde[i], wv[i]))
    conds_p.append(c)
BMLp = [split_s(c) for c in conds_p]
assert all(eval_cond(bml, pt0, ps0) == 0 for bml in BMLp)          # (a) conditions vanish
minorsp = [det3([BMLp[i], BMLp[j], BMLp[k]]) for i, j, k in itertools.combinations(range(7), 3)]
assert all(evalp(mn, pt0, (0, 0)) == 0 for mn in minorsp)         # (b) minors vanish at t0
# (c) the machinery distinguishes: original 7x3 condition matrix at pt0 has full
#     rank 3 (obstructed -- no (s1,s2) satisfies it), planted has rank <= 2
#     (consistent).  (The planted minors are inhomogeneous -- b~ acquired a constant
#     term -- so the homogeneous rank-6 span criterion does not apply to them;
#     the rank drop of the condition matrix is the correct comparison.)
def cond_matrix(BMLx, t):
    return [[evalp(b, t, (0, 0)), evalp(m, t, (0, 0)), evalp(l, t, (0, 0))]
            for (b, m, l) in BMLx]
def num_rank(rows):
    _, piv = rref([r[:] for r in rows], len(rows[0]))
    return len(piv)
r_orig = num_rank(cond_matrix(BML, pt0))
r_plant = num_rank(cond_matrix(BMLp, pt0))
assert r_orig == 3 and r_plant <= 2
Rtilde_at = [evalp(r, pt0, ps0) for r in Rtilde]
sol = solve(M2, [(-x) % Rr for x in Rtilde_at], len(B0_))
assert sol is not None and all(((a + b) % Rr) == 0                # (d) planted E2 solvable
                               for a, b in zip(matvec(M2, sol), Rtilde_at))
assert any(evalp(mn, pt0, (0, 0)) != 0 for mn in minors)          # (e) t0 was obstructed
print(f"planted control at (t,s)={pt0},{ps0}: 7 conditions vanish at planted point: True; "
      f"35 planted minors vanish at t0: True; condition-matrix rank {r_orig} -> {r_plant}: True; "
      f"planted E2 directly solvable: True")

# 5b. cubic planted control: subtract delta_i*(t1/t0_1)^3 from each b_i, keeping the
#     conditions homogeneous cubic in t, so the 35 minors stay homogeneous quintics.
#     This tests the final rank-6 step against a known-good case: the minor rank must
#     drop from 6 to 5.
t01_cubed_inv = fmpq_poly([fmpq(1, pt0[0] ** 3)])              # (t1/t0_1)^3 = t1^3/64
cubic = {(3, 0, 0, 0): t01_cubed_inv}
BMLc = []
for (b, m, l) in BML:
    delta = (evalp(b, pt0, (0, 0)) + ps0[0] * evalp(m, pt0, (0, 0))
             + ps0[1] * evalp(l, pt0, (0, 0)))
    BMLc.append((padd(b, pscale(cubic, (-delta) % Rr)), m, l))
assert all((evalp(b, pt0, ps0) + ps0[0] * evalp(m, pt0, ps0)
            + ps0[1] * evalp(l, pt0, ps0)) == 0 for (b, m, l) in BMLc)
minorsc = [det3([BMLc[i], BMLc[j], BMLc[k]]) for i, j, k in itertools.combinations(range(7), 3)]
assert all(all(k in quint for k in mc) for mc in minorsc)     # still homogeneous quintics
assert all(evalp(mc, pt0, (0, 0)) == 0 for mc in minorsc)
Cc = [[mc.get(q, Z) for q in quint] for mc in minorsc]
_, rkc = rref(Cc, 6)
print(f"cubic planted control: 35 homogeneous minors vanish at t0: True; "
      f"minor rank 6 -> {len(rkc)}: True")
assert len(rkc) == 5

# 6. end-to-end residual check (not tautological): plug numeric (t,s) into the constructed
#    A1,B2,A0,B1 and evaluate the ORIGINAL weight -3 and -2 bracket equations directly from the
#    generator; both must vanish exactly.  Then compare the E2 inhomogeneity R evaluated
#    symbolically vs directly.
for t0, s0 in (((2, 3), (5, 7)), ((-1, 4), (0, 11))):
    num = dict(top)
    for u in T_: num[u] = evalp(tval[u], t0, s0)
    for u in X_: num[u] = evalp(xval[u], t0, s0)
    res = {}
    for W in (-3, -2):
        bad = 0
        for k in blocks[W]:
            acc = Z
            for c, pv, qv in eqs[k]:
                acc = (acc + c * num[pv] * num[qv]) % Rr
            bad += (acc != 0)
        res[W] = bad
    Rnum = []
    for k in blocks[-1]:
        acc = Z
        for c, pv, qv in eqs[k]:
            if pv in num and qv in num and pv not in top and qv not in top:
                acc = (acc + c * num[pv] * num[qv]) % Rr
        Rnum.append(acc)
    agree = all(evalp(r, t0, s0) == rn for r, rn in zip(Rt, Rnum))
    print(f"(t,s)={t0},{s0}: nonvanishing weight -3 eqs: {res[-3]}, weight -2 eqs: {res[-2]};  E2 inhomogeneity symbolic==direct: {agree}")
