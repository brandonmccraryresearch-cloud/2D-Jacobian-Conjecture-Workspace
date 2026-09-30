#!/usr/bin/env python3
"""
branch_c_stage3_e1_descent.py — Branch (c) Stage 3.

Part 1: Extract the E_2 hypersurface H(t,s) = W_1 . RHS_{E_2}(t,s).
  - Reconstruct E_4 kernel (t-directions for A_1, B_2).
  - Solve E_3: particular (quadratic in t) + kernel (s-directions) for A_0, B_1.
  - Build RHS_{E_2}(t,s) = 2*A_0'*B_2 - (A_1*B_1' - A_1'*B_1).
  - Contract with W_1 (from Stage 2). Analyze the polynomial structure.

Part 2: The E_1 layer operator.
  - A_{-2}(u): u-exponents 0..6 (7 unknowns). B_{-1}(u): u-exponents 0..11 (12 unknowns).
  - O_{E_1} = -(2*A_{-2}*B_3' + 3*A_{-2}'*B_3) + (2*A_2*B_{-1}' + A_2'*B_{-1}).
  - 19x19 matrix. Exact rank over K_5, mod-101 cross-check.
  - Left nullspace dimension and compatibility conditions.

Run with: ~/miniconda3/envs/physics/bin/python branch_c_stage3_e1_descent.py
"""

import json
import sys
from flint import fmpq_poly, fmpq, nmod_poly

sys.path.insert(0, "/home/hatch/workspace/v18/branch_ab_v19/lean/certgen")
from gen_system import build

# ---------------------------------------------------------------- K_5 setup
Rr = fmpq_poly([26, 0, 3, 3, -1, 1])

def K(coeffs):
    return fmpq_poly([fmpq(*map(int, c.split('/'))) if '/' in c
                      else fmpq(int(c)) for c in coeffs]) % Rr

def kinv(a):
    g, s, _ = a.xgcd(Rr)
    assert g == 1
    return s % Rr

ZERO = fmpq_poly([0])
ONE = fmpq_poly([1])

# ------------------------------------------------- Load K_5 point + system
d = json.load(open("/home/hatch/workspace/v18/branch_ab_v19/lean/certgen/e5_exact_K5.json"))
pt = {v: K(c) for v, c in d.items() if not v.startswith("_")}
pt.update({"a_1_0": ONE, "b_2_1": ONE, "a_2_2": ONE})

LP, LQ, eqs, tgt = build()
w = lambda ij: ij[1] - 2 * ij[0]
vw = lambda v: w(tuple(map(int, v.split('_')[1:])))

def jacobian(weight, unknowns):
    rows = []
    for k in sorted(eqs):
        if w(k) != weight:
            continue
        row = [ZERO] * len(unknowns)
        idx = {u: i for i, u in enumerate(unknowns)}
        for c, pv, qv in eqs[k]:
            for a, b in ((pv, qv), (qv, pv)):
                if a in idx and b in pt:
                    row[idx[a]] = (row[idx[a]] + c * pt[b]) % Rr
        rows.append(row)
    return rows

def nullspace(M, ncols):
    M = [r[:] for r in M]
    piv, r = [], 0
    for c in range(ncols):
        i = next((i for i in range(r, len(M)) if M[i][c] != ZERO), None)
        if i is None:
            continue
        M[r], M[i] = M[i], M[r]
        iv = kinv(M[r][c])
        M[r] = [(x * iv) % Rr for x in M[r]]
        for j in range(len(M)):
            if j != r and M[j][c] != ZERO:
                f = M[j][c]
                M[j] = [(M[j][l] - f * M[r][l]) % Rr for l in range(ncols)]
        piv.append(c); r += 1
    basis = []
    for f in [c for c in range(ncols) if c not in piv]:
        v = [ZERO] * ncols; v[f] = ONE
        for i, pc in enumerate(piv):
            v[pc] = (-M[i][f]) % Rr
        basis.append(v)
    return basis, piv, M

key = lambda v: (v[0], int(v.split('_')[1]), int(v.split('_')[2]))
allv = sorted({v for T in eqs.values() for c, pv, qv in T for v in (pv, qv)}, key=key)
A1B2 = [v for v in allv if (v[0] == 'a' and vw(v) == -1) or (v[0] == 'b' and vw(v) == -2)]
A0B1 = [v for v in allv if (v[0] == 'a' and vw(v) == 0 and v != 'a_0_0') or (v[0] == 'b' and vw(v) == -1)]

print("=" * 70)
print("PART 1: THE E_2 HYPERSURFACE H(t,s)")
print("=" * 70)

# ------------------------------------------------- E_4 kernel (t-directions)
M4 = jacobian(-3, A1B2)
k4, piv4, _ = nullspace(M4, len(A1B2))
assert len(k4) == 2
print(f"E_4: {len(M4)}x{len(A1B2)}, kernel dim {len(k4)}")

# tval[u] = { (1,0): coeff of t1, (0,1): coeff of t2 } for u in A1B2
tval = {u: {(1, 0): k4[0][i], (0, 1): k4[1][i]} for i, u in enumerate(A1B2)}

# ------------------------------------------------- E_3: K(t) quadratic, solve for particular + kernel
def qadd(a, b):
    c = dict(a)
    for k, v in b.items():
        c[k] = (c.get(k, ZERO) + v) % Rr
    return {k: v for k, v in c.items() if v != ZERO}

def qmul(a, b):
    c = {}
    for (e1, e2), v1 in a.items():
        for (f1, f2), v2 in b.items():
            k = (e1 + f1, e2 + f2)
            c[k] = (c.get(k, ZERO) + v1 * v2) % Rr
    return {k: v for k, v in c.items() if v != ZERO}

# K(t): for each weight -2 equation, sum over bilinear terms in (A1,B2)
Kt = []  # list of dicts {(e1,e2): K5 coeff}, one per equation
eq_keys_w2 = [k for k in sorted(eqs) if w(k) == -2]
for k in eq_keys_w2:
    acc = {}
    for c, pv, qv in eqs[k]:
        if pv in tval and qv in tval:
            prod = qmul(tval[pv], tval[qv])
            acc = qadd(acc, {kk: (vv * c) % Rr for kk, vv in prod.items()})
    Kt.append(acc)

M3 = jacobian(-2, A0B1)
k3, piv3, rref3 = nullspace(M3, len(A0B1))
assert len(k3) == 2
print(f"E_3: {len(M3)}x{len(A0B1)}, kernel dim {len(k3)}")

# Particular solution: solve M3 x = -K(t) for x as quadratic in t.
# For each t-monomial (2,0),(1,1),(0,2), solve the linear system.
def solve_lin(M, piv, rref, rhs):
    """Solve M x = rhs using rref (piv, rref from nullspace). Returns x or None."""
    ncols = len(M[0])
    # Augment: use rref rows. rref[i] has pivot at piv[i].
    # x[piv[i]] = rhs'[i] - sum_{free} rref[i][f] x[f]; set free = 0.
    # First transform rhs by the same row ops: we need the transformed rhs.
    # Since nullspace() did Gauss-Jordan, rref[i][piv[i]] = 1.
    # The row ops are encoded in rref; to get particular, do forward elimination on rhs.
    # Simpler: redo elimination with augmented matrix.
    aug = [M[i][:] + [rhs[i]] for i in range(len(M))]
    nc = ncols
    piv2, r = [], 0
    for c in range(nc):
        i = next((i for i in range(r, len(aug)) if aug[i][c] != ZERO), None)
        if i is None:
            continue
        aug[r], aug[i] = aug[i], aug[r]
        iv = kinv(aug[r][c])
        aug[r] = [(x * iv) % Rr for x in aug[r]]
        for j in range(len(aug)):
            if j != r and aug[j][c] != ZERO:
                f = aug[j][c]
                aug[j] = [(aug[j][l] - f * aug[r][l]) % Rr for l in range(nc + 1)]
        piv2.append(c); r += 1
    # Check consistency: zero rows must have zero rhs
    for i in range(r, len(aug)):
        if aug[i][nc] != ZERO:
            return None
    x = [ZERO] * nc
    for i, pc in enumerate(piv2):
        x[pc] = aug[i][nc]
    return x

# Solve for each t-monomial
tmonos = [(2, 0), (1, 1), (0, 2)]
part = {}  # u -> {(e1,e2): coeff}  (quadratic part of A0,B1)
for tm in tmonos:
    rhs = [ZERO] * len(M3)
    for i, q in enumerate(Kt):
        rhs[i] = (-q.get(tm, ZERO)) % Rr
    sol = solve_lin(M3, piv3, rref3, rhs)
    assert sol is not None, f"E_3 not solvable for t-monomial {tm}!"
    for j, u in enumerate(A0B1):
        if sol[j] != ZERO:
            part.setdefault(u, {})[tm] = sol[j]

print(f"E_3 particular solution: {len(part)} variables have nonzero quadratic part")

# Full (t,s)-parameterization:
# aval[u] = dict {(e1,e2,e3,e4): coeff} for t1^e1 t2^e2 s1^e3 s2^e4
def to44(d2, s_idx=None):
    """Lift {(e1,e2): c} to {(e1,e2,0,0): c}; if s_idx given, add s-monomial."""
    out = {}
    for (e1, e2), c in d2.items():
        key = [e1, e2, 0, 0]
        if s_idx is not None:
            key[2 + s_idx] = 1
        out[tuple(key)] = c
    return out

aval = {}  # variable -> {(e1,e2,e3,e4): K5}
for u in A1B2:
    aval[u] = to44(tval[u])
for u in A0B1:
    d = {}
    if u in part:
        d.update(to44(part[u]))
    # kernel: s1*k3[0] + s2*k3[1]
    j = A0B1.index(u)
    if k3[0][j] != ZERO:
        d[(0, 0, 1, 0)] = (d.get((0, 0, 1, 0), ZERO) + k3[0][j]) % Rr
    if k3[1][j] != ZERO:
        d[(0, 0, 0, 1)] = (d.get((0, 0, 0, 1), ZERO) + k3[1][j]) % Rr
    aval[u] = {k: v for k, v in d.items() if v != ZERO}

# ------------------------------------------------- Build RHS_{E_2}(t,s) as u-polynomial with (t,s)-coeffs
# RHS = 2*A_0'*B_2 - A_1*B_1' + A_1'*B_1
# Variables: A_0 (a, w=0), B_2 (b, w=-2), A_1 (a, w=-1), B_1 (b, w=-1)

def var_u_exp(v):
    """u-exponent of variable v = a_i_j or b_i_j."""
    return int(v.split('_')[1])

def poly_of_var(v):
    """{u-exp: (t,s)-poly} for variable v."""
    return {var_u_exp(v): aval[v]}

def ts_add(p, q, sign=1):
    r = dict(p)
    for k, v in q.items():
        r[k] = (r.get(k, ZERO) + sign * v) % Rr
    return {k: v for k, v in r.items() if v != ZERO}

def ts_mul(p, q):
    r = {}
    for k1, v1 in p.items():
        for k2, v2 in q.items():
            k = (k1[0] + k2[0], k1[1] + k2[1], k1[2] + k2[2], k1[3] + k2[3])
            r[k] = (r.get(k, ZERO) + v1 * v2) % Rr
    return {k: v for k, v in r.items() if v != ZERO}

def upoly_add(P, Q, sign=1):
    r = dict(P)
    for e, p in Q.items():
        r[e] = ts_add(r.get(e, {}), p, sign)
        if not r[e]:
            del r[e]
    return r

def upoly_mul(P, Q):
    r = {}
    for e1, p1 in P.items():
        for e2, p2 in Q.items():
            e = e1 + e2
            pr = ts_mul(p1, p2)
            r[e] = ts_add(r.get(e, {}), pr)
            if not r[e]:
                del r[e]
    return r

def upoly_deriv(P):
    return {e - 1: {k: (v * e) % Rr for k, v in p.items()}
            for e, p in P.items() if e > 0}

def upoly_scale(P, s):
    return {e: {k: (v * s) % Rr for k, v in p.items()} for e, p in P.items()}

# Assemble A_0, B_2, A_1, B_1 as u-polys
A0_vars = [v for v in A0B1 if v[0] == 'a']
B2_vars = [v for v in A1B2 if v[0] == 'b']
A1_vars = [v for v in A1B2 if v[0] == 'a']
B1_vars = [v for v in A0B1 if v[0] == 'b']

def assemble(vars):
    P = {}
    for v in vars:
        P = upoly_add(P, poly_of_var(v))
    return P

A0 = assemble(A0_vars)
B2 = assemble(B2_vars)
A1 = assemble(A1_vars)
B1 = assemble(B1_vars)

A0d = upoly_deriv(A0)
B1d = upoly_deriv(B1)
A1d = upoly_deriv(A1)

# RHS = 2*A_0'*B_2 - A_1*B_1' + A_1'*B_1
RHS = upoly_add(upoly_scale(upoly_mul(A0d, B2), 2),
                upoly_add(upoly_scale(upoly_mul(A1, B1d), -1),
                          upoly_mul(A1d, B1)))
print(f"RHS_{{E_2}}: u-exponents {sorted(RHS.keys())}")

# ------------------------------------------------- Contract with W_1 from Stage 2
# Recompute W_1 (left nullvector of E_2 operator) — import from stage2 logic
# For self-containment, rebuild the E_2 operator and extract W_1.
A2c = {}
for i in range(1, 9):
    A2c[i] = pt.get(f"a_{i}_{2*i-2}", ZERO)
B3c = {}
for i in range(2, 13):
    B3c[i] = pt.get(f"b_{i}_{2*i-3}", ZERO)

def dmul(p, q):
    r = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            e = e1 + e2
            r[e] = (r.get(e, ZERO) + c1 * c2) % Rr
    return {e: v for e, v in r.items() if v != ZERO}

def dderiv(p):
    return {e-1: (c*e) % Rr for e, c in p.items() if e > 0}

B3d = dderiv(B3c)
N_ROWS, N_B0, N_Am1 = 19, 12, 8
N_COLS = N_B0 + N_Am1
M = [[ZERO]*N_COLS for _ in range(N_ROWS)]
for j in range(1, 13):
    for e, c in A2c.items():
        ue = e + j - 1
        if 1 <= ue <= 19:
            M[ue-1][j-1] = (M[ue-1][j-1] + 2*j*c) % Rr
for i in range(0, 8):
    for e, c in B3d.items():
        ue = e + i
        if 1 <= ue <= 19:
            M[ue-1][N_B0+i] = (M[ue-1][N_B0+i] - c) % Rr
    if i > 0:
        for e, c in B3c.items():
            ue = e + i - 1
            if 1 <= ue <= 19:
                M[ue-1][N_B0+i] = (M[ue-1][N_B0+i] - 3*i*c) % Rr

MT = [[M[r][c] for r in range(N_ROWS)] for c in range(N_COLS)]
kT, pivT, rrefT = nullspace(MT, N_ROWS)
assert len(kT) == 1
W1 = kT[0]  # left nullvector, indexed by u-exp - 1
print(f"W_1: nonzero on u-exponents {[i+1 for i,w in enumerate(W1) if w!=ZERO]}")

# H(t,s) = sum_e W1[e] * RHS[e]
H = {}
for e, p in RHS.items():
    wv = W1[e-1]
    if wv == ZERO:
        continue
    for k, v in p.items():
        H[k] = (H.get(k, ZERO) + wv * v) % Rr
H = {k: v for k, v in H.items() if v != ZERO}

print(f"\nH(t,s) has {len(H)} monomials in (t1,t2,s1,s2):")
for k in sorted(H):
    print(f"  t1^{k[0]} t2^{k[1]} s1^{k[2]} s2^{k[3]}: {H[k]}")

# Analyze structure: separate b(t), s1*M(t), s2*L(t)
b = {k: v for k, v in H.items() if k[2] == 0 and k[3] == 0}
Mcoef = {k: v for k, v in H.items() if k[2] == 1 and k[3] == 0}
Lcoef = {k: v for k, v in H.items() if k[2] == 0 and k[3] == 1}
other = {k: v for k, v in H.items() if not (k in b or k in Mcoef or k in Lcoef)}
print(f"\nb(t) monomials: {len(b)}, degrees: {sorted(set(k[0]+k[1] for k in b))}")
print(f"s1*M(t) monomials: {len(Mcoef)}")
print(f"s2*L(t) monomials: {len(Lcoef)}")
print(f"other (nonlinear in s): {len(other)}")
M_zero = (len(Mcoef) == 0)
L_zero = (len(Lcoef) == 0)
print(f"M(t) identically zero: {M_zero}")
print(f"L(t) identically zero: {L_zero}")
if other:
    print("WARNING: H has terms nonlinear in s!")
    for k in sorted(other):
        print(f"  t1^{k[0]} t2^{k[1]} s1^{k[2]} s2^{k[3]}")

print("\n" + "=" * 70)
print("PART 2: THE E_1 LAYER OPERATOR")
print("=" * 70)

# A_{-2}: P k=-2, u-exponents 0..6 (7 unknowns)
# B_{-1}: Q l=-1, u-exponents 0..11 (12 unknowns)
# O = -(2*A_{-2}*B_3' + 3*A_{-2}'*B_3) + (2*A_2*B_{-1}' + A_2'*B_{-1})
A2d = dderiv(A2c)

def build_E1():
    rows = {}  # u-exp -> list of 19 coeffs
    NC = 7 + 12
    # A_{-2} columns (0..6): coeff of a_{-2,i} in -(2*A_{-2}*B_3' + 3*A_{-2}'*B_3)
    for i in range(0, 7):
        col = {}
        for e, c in B3d.items():  # -2*A_{-2}*B_3'
            ue = e + i
            col[ue] = (col.get(ue, ZERO) - 2*c) % Rr
        if i > 0:  # -3*A_{-2}'*B_3
            for e, c in B3c.items():
                ue = e + i - 1
                col[ue] = (col.get(ue, ZERO) - 3*i*c) % Rr
        for ue, v in col.items():
            rows.setdefault(ue, [ZERO]*NC)[i] = v
    # B_{-1} columns (7..18): coeff of b_{-1,j} in (2*A_2*B_{-1}' + A_2'*B_{-1})
    for j in range(0, 12):
        col = {}
        if j > 0:  # 2*A_2*B_{-1}': B_{-1}' contributes j*b_{-1,j} u^{j-1}
            for e, c in A2c.items():
                ue = e + j - 1
                col[ue] = (col.get(ue, ZERO) + 2*j*c) % Rr
        for e, c in A2d.items():  # A_2'*B_{-1}
            ue = e + j
            col[ue] = (col.get(ue, ZERO) + c) % Rr
        for ue, v in col.items():
            rows.setdefault(ue, [ZERO]*NC)[7+j] = v
    return rows

E1rows = build_E1()
uexps = sorted(E1rows.keys())
print(f"E_1 operator: u-exponents {uexps[0]}..{uexps[-1]} ({len(uexps)} equations)")
print(f"Unknowns: 7 (A_{{-2}}) + 12 (B_{{-1}}) = 19")
M1 = [E1rows[e] for e in uexps]
assert len(M1) == 19 and len(M1[0]) == 19

def rank_of(rows):
    M = [r[:] for r in rows]
    nr, nc = len(M), len(M[0])
    r = 0
    for c in range(nc):
        piv = next((i for i in range(r, nr) if M[i][c] != ZERO), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        iv = kinv(M[r][c])
        M[r] = [(x*iv) % Rr for x in M[r]]
        for i in range(nr):
            if i != r and M[i][c] != ZERO:
                f = M[i][c]
                M[i] = [(M[i][j] - f*M[r][j]) % Rr for j in range(nc)]
        r += 1
    return r, M

rk1, _ = rank_of(M1)
print(f"Rank over K_5 (exact): {rk1}")
print(f"Left nullspace dimension: {len(M1) - rk1}")
print(f"Kernel dimension (new params): {len(M1[0]) - rk1}")

# Mod-101 cross-check
Rm101 = nmod_poly([26, 0, 3, 3, -1, 1], 101)
rt = next(w for w in range(101) if Rm101(w) == 0)
def m101(a):
    t = 0
    for k, ck in enumerate(list(a)):
        t = (t + int(ck.numerator) % 101 * pow(int(ck.denominator) % 101, 99, 101) % 101 * pow(rt, k, 101)) % 101
    return t
M1_101 = [[m101(x) for x in row] for row in M1]
def rank101(rows):
    M = [r[:] for r in rows]
    nr, nc = len(M), len(M[0])
    r = 0
    for c in range(nc):
        piv = next((i for i in range(r, nr) if M[i][c] % 101 != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        iv = pow(M[r][c], 99, 101)
        M[r] = [(x*iv) % 101 for x in M[r]]
        for i in range(nr):
            if i != r and M[i][c] % 101 != 0:
                f = M[i][c]
                M[i] = [(M[i][j] - f*M[r][j]) % 101 for j in range(nc)]
        r += 1
    return r
print(f"Rank mod 101: {rank101(M1_101)}")

print("\n" + "=" * 70)
print("STAGE 3 SUMMARY")
print("=" * 70)
print(f"H(t,s): {len(H)} monomials; b(t) cubic: {len(b)} terms; "
      f"M==0: {M_zero}; L==0: {L_zero}; nonlinear-in-s: {len(other)}")
print(f"E_1: 19x19, rank {rk1}, left nullity {len(M1)-rk1}, "
      f"kernel dim {len(M1[0])-rk1}")
