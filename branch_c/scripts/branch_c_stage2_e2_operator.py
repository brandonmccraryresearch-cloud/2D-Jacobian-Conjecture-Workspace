#!/usr/bin/env python3
"""
branch_c_stage2_e2_operator.py — Branch (c) Stage 2: the E_2 layer operator.

Source: Julian's colleague's layer-algebra directive (2026-09-28).

Mathematical setup:
  E_5, E_4, E_3 are PROVEN identical to Branch (a,b) (no negative layers can
  enter: k+l = 5, 4, 3 with k<=2, l<=3 forces k,l >= 0).
  E_2 (M=1, y^{-1}): k+l = 2. Pairs: (0,2), (1,1), (2,0) [known from (a,b)]
  PLUS the first negative pair (-1,3) [new in Branch (c)].

  E_2 equation:
    2*A_2*B_0' - (A_{-1}*B_3' + 3*A_{-1}'*B_3) = RHS_{E_2}(t,s)

  Unknowns (20): b_{0,1}..b_{0,12} (B_0, u-exponents 1..12),
                 a_{-1,0}..a_{-1,7} (A_{-1}, u-exponents 0..7).
  Equations (19): coefficients of u^1 .. u^19.

  A_2, B_3 are the certified K_5 E_5-point from v19 (e5_exact_K5.json).

Computes:
  1. Exact 19x20 operator matrix over K_5 = Q[w]/(w^5-w^4+3w^3+3w^2+26).
  2. Rank over K_5 (exact) and mod 101 (cross-check).
  3. Left nullspace dimension = 19 - rank.
  4. If rank < 19: the surviving compatibility conditions.

Run with: ~/miniconda3/envs/physics/bin/python branch_c_stage2_e2_operator.py
"""

import json
import sys
from flint import fmpq_poly, fmpq, nmod_poly

# ---------------------------------------------------------------- K_5 setup
Rr = fmpq_poly([26, 0, 3, 3, -1, 1])  # w^5 - w^4 + 3w^3 + 3w^2 + 26

def K(coeffs):
    """Rational coefficient list (power basis) -> element of K_5."""
    return fmpq_poly([fmpq(*map(int, c.split('/'))) if '/' in c
                      else fmpq(int(c)) for c in coeffs]) % Rr

def kinv(a):
    g, s, _ = a.xgcd(Rr)
    assert g == 1, "non-invertible element!"
    return s % Rr

ZERO = fmpq_poly([0])
ONE = fmpq_poly([1])

# ------------------------------------------------- Load certified K_5 point
import os as _os, shutil as _shutil  # configurable paths (defaults = the original machine)
CERTGEN = _os.environ.get("BRANCH_C_CERTGEN", "/home/hatch/workspace/v18/branch_ab_v19/lean/certgen")
WORKDIR = _os.environ.get("BRANCH_C_WORKDIR", "/home/hatch/workspace")
SINGULAR = _os.environ.get("SINGULAR", "/home/hatch/miniconda3/envs/cas/bin/Singular")
if "SINGULAR" not in _os.environ and not _os.path.exists(SINGULAR): SINGULAR = _shutil.which("Singular") or SINGULAR
d = json.load(open(_os.path.join(CERTGEN, "e5_exact_K5.json")))
pt = {v: K(c) for v, c in d.items() if not v.startswith("_")}
pt.update({"a_1_0": ONE, "b_2_1": ONE, "a_2_2": ONE})  # normalisation

def get(var):
    return pt.get(var, ZERO)

# A_2(u) = sum_{j-2i=-2} a_{i,j} u^i,  i = 1..8
A2_coeffs = {}  # u-exponent -> K_5 element
for i in range(1, 9):
    j = 2 * i - 2
    A2_coeffs[i] = get(f"a_{i}_{j}")

# B_3(u) = sum_{j-2i=-3} b_{i,j} u^i,  i = 2..12
B3_coeffs = {}
for i in range(2, 13):
    j = 2 * i - 3
    B3_coeffs[i] = get(f"b_{i}_{j}")

print("A_2(u) u-exponents:", sorted(A2_coeffs.keys()))
print("B_3(u) u-exponents:", sorted(B3_coeffs.keys()))
print("A_2 has nonzero constant term:", A2_coeffs.get(0, ZERO) != ZERO)
print("B_3 leading structure ok:", B3_coeffs[2] == ONE)

# ------------------------------------------------- Polynomial arithmetic over K_5
def poly_mul(p, q):
    """Multiply dict-based polys over K_5."""
    r = {}
    for e1, c1 in p.items():
        if c1 == ZERO:
            continue
        for e2, c2 in q.items():
            if c2 == ZERO:
                continue
            e = e1 + e2
            r[e] = (r.get(e, ZERO) + c1 * c2) % Rr
    return r

def poly_deriv(p):
    """d/du of dict-based poly."""
    return {e - 1: (c * e) % Rr for e, c in p.items() if e > 0 and c != ZERO}

def poly_add(p, q, sign=1):
    r = dict(p)
    for e, c in q.items():
        if c == ZERO:
            continue
        r[e] = (r.get(e, ZERO) + sign * c) % Rr
        if r[e] == ZERO:
            del r[e]
    return r

# ------------------------------------------------- Build the 19x20 operator
# Unknowns x = (b_{0,1}..b_{0,12}, a_{-1,0}..a_{-1,7})
# Operator: 2*A_2*B_0' - (A_{-1}*B_3' + 3*A_{-1}'*B_3)
# Rows: coefficients of u^1 .. u^19.

B3d = poly_deriv(B3_coeffs)
A2d = poly_deriv(A2_coeffs)  # not needed directly, but for reference

N_ROWS = 19  # u^1 .. u^19
N_B0 = 12    # b_{0,1}..b_{0,12}
N_Am1 = 8    # a_{-1,0}..a_{-1,7}
N_COLS = N_B0 + N_Am1

def col_B0(j):
    """Column for b_{0,j} (j=1..12): coefficient of b_{0,j} in 2*A_2*B_0'."""
    # B_0 = sum_j b_{0,j} u^j; B_0' contributes j*b_{0,j} u^{j-1}.
    # 2*A_2*B_0': coefficient of b_{0,j} is 2*j * (A_2 shifted by j-1).
    col = {}
    for e, c in A2_coeffs.items():
        if c == ZERO:
            continue
        uexp = e + (j - 1)
        if 1 <= uexp <= 19:
            col[uexp] = (col.get(uexp, ZERO) + 2 * j * c) % Rr
    return col

def col_Am1(i):
    """Column for a_{-1,i} (i=0..7): coeff of a_{-1,i} in -(A_{-1}*B_3' + 3*A_{-1}'*B_3)."""
    # A_{-1} = sum_i a_{-1,i} u^i.
    # Term 1: -A_{-1}*B_3': coeff of a_{-1,i} is -(B_3' shifted by i).
    # Term 2: -3*A_{-1}'*B_3: A_{-1}' contributes i*a_{-1,i} u^{i-1};
    #         coeff of a_{-1,i} is -3*i*(B_3 shifted by i-1).
    col = {}
    for e, c in B3d.items():
        if c == ZERO:
            continue
        uexp = e + i
        if 1 <= uexp <= 19:
            col[uexp] = (col.get(uexp, ZERO) - c) % Rr
    if i > 0:
        for e, c in B3_coeffs.items():
            if c == ZERO:
                continue
            uexp = e + (i - 1)
            if 1 <= uexp <= 19:
                col[uexp] = (col.get(uexp, ZERO) - 3 * i * c) % Rr
    return col

# Assemble matrix as list of rows, each row a list of K_5 elements
M = [[ZERO] * N_COLS for _ in range(N_ROWS)]
for j in range(1, 13):
    col = col_B0(j)
    for uexp, val in col.items():
        M[uexp - 1][j - 1] = val
for i in range(0, 8):
    col = col_Am1(i)
    for uexp, val in col.items():
        M[uexp - 1][N_B0 + i] = val

print(f"\nOperator matrix: {N_ROWS} x {N_COLS} over K_5")

# ------------------------------------------------- Exact rank over K_5
def rank_and_rref(rows):
    """Exact Gaussian elimination over K_5. Returns (rank, rref_rows, pivot_cols)."""
    M = [r[:] for r in rows]
    nrows, ncols = len(M), len(M[0]) if M else 0
    pivots = []
    r = 0
    for c in range(ncols):
        piv = next((i for i in range(r, nrows) if M[i][c] != ZERO), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        iv = kinv(M[r][c])
        M[r] = [(x * iv) % Rr for x in M[r]]
        for i in range(nrows):
            if i != r and M[i][c] != ZERO:
                f = M[i][c]
                M[i] = [(M[i][j] - f * M[r][j]) % Rr for j in range(ncols)]
        pivots.append(c)
        r += 1
    return r, M, pivots

rankK5, rrefK5, pivK5 = rank_and_rref(M)
print(f"Rank over K_5 (exact, char 0): {rankK5}")
print(f"Left nullspace dimension over K_5: {N_ROWS - rankK5}")

# ------------------------------------------------- Mod-101 cross-check
# Reduce the K_5 point mod 101: need a root of R mod 101.
Rm101 = nmod_poly([26, 0, 3, 3, -1, 1], 101)
root = None
for w in range(101):
    if Rm101(w) == 0:
        root = w
        break
assert root is not None, "R has no root mod 101?"
print(f"\nMod-101 check: using root w = {root} of R mod 101")

def to_m101(a):
    """Evaluate K_5 element (fmpq_poly) at w=root mod 101."""
    # a is sum c_k w^k with c_k = p/q; compute sum (p * q^{-1}) root^k mod 101
    total = 0
    coeffs = a.coeffs()  # highest-first? check below
    # fmpq_poly coeffs: use list(a) for lowest-first
    for k, ck in enumerate(list(a)):
        num = int(ck.numerator) % 101
        den = int(ck.denominator) % 101
        deninv = pow(den, 99, 101)
        total = (total + num * deninv % 101 * pow(root, k, 101)) % 101
    return total

M101 = [[to_m101(M[r][c]) for c in range(N_COLS)] for r in range(N_ROWS)]

def rank_m101(rows):
    M = [r[:] for r in rows]
    nrows, ncols = len(M), len(M[0])
    r = 0
    pivots = []
    for c in range(ncols):
        piv = next((i for i in range(r, nrows) if M[i][c] % 101 != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        iv = pow(M[r][c], 99, 101)
        M[r] = [(x * iv) % 101 for x in M[r]]
        for i in range(nrows):
            if i != r and M[i][c] % 101 != 0:
                f = M[i][c]
                M[i] = [(M[i][j] - f * M[r][j]) % 101 for j in range(ncols)]
        pivots.append(c)
        r += 1
    return r, M, pivots

rank101, rref101, piv101 = rank_m101(M101)
print(f"Rank mod 101: {rank101}")
print(f"Left nullspace dimension mod 101: {N_ROWS - rank101}")

# ------------------------------------------------- Verdict
print("\n" + "=" * 70)
print("STAGE 2 VERDICT")
print("=" * 70)
if rankK5 == 19:
    print("RANK 19: operator is SURJECTIVE (full row rank).")
    print("E_2 is unconditionally solvable — NO compatibility conditions on (t,s).")
    print("The descent proceeds to E_1 unobstructed at this layer.")
else:
    print(f"RANK {rankK5} < 19: LEFT NULLSPACE DIMENSION = {N_ROWS - rankK5}.")
    print("Surviving compatibility conditions W . RHS_{E_2}(t,s) = 0:")
    # Extract left nullvectors from the K_5 rref: zero rows of rref give
    # relations, but we need the actual nullvectors. Recompute via transpose.
    MT = [[M[r][c] for r in range(N_ROWS)] for c in range(N_COLS)]  # 20x19
    # Nullspace of M^T... actually left null of M = null of M^T (as 19-dim vectors y with y^T M = 0)
    # i.e., M^T y = 0 where M^T is 20x19. Compute nullspace of the 20x19 matrix.
    rkT, rrefT, pivT = rank_and_rref(MT)
    freecols = [c for c in range(N_ROWS) if c not in pivT]
    print(f"  (computed via transpose: rank {rkT}, free cols {freecols})")
    nullvecs = []
    for f in freecols:
        v = [ZERO] * N_ROWS
        v[f] = ONE
        for i, p in enumerate(pivT):
            v[p] = (-rrefT[i][f]) % Rr
        nullvecs.append(v)
    print(f"  Number of independent left nullvectors: {len(nullvecs)}")
    # Report their u-support (which equations they involve)
    for idx, v in enumerate(nullvecs):
        supp = [e + 1 for e, val in enumerate(v) if val != ZERO]
        print(f"  W_{idx + 1}: supported on u-exponents {supp}")

print("\nSummary dict:")
print({"rank_K5": rankK5, "rank_101": rank101,
       "left_null_K5": N_ROWS - rankK5, "left_null_101": N_ROWS - rank101})
