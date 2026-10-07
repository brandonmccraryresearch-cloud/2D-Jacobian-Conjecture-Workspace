"""lu_fill.py -- the size of an elimination (LU) certificate for the pivot block M_S, as the alternative to the
explicit inverse.  Pivot columns from FLINT rref mod p (as make_inverse.py); sparse LU of M_S with scipy's SuperLU
under several column orderings, over floats, which gives the fill pattern; reported: nnz(L), nnz(U), and the cost of
checking L U = P M_S Q entry by entry, sum_k |L(:,k)| |U(k,:)| multiply-adds.
usage: python3 lu_fill.py MATRIX.pkl      (MATRIX.pkl from ../build_matrix.py; needs python-flint, numpy, scipy)
"""
import sys, pickle, time
import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spla
from flint import nmod_mat

d = pickle.load(open(sys.argv[1], "rb"))
p, rows, cols, colv = d["p"], d["rows"], d["cols"], d["colv"]
nr, nc = len(rows), len(cols)
t0 = time.time()
A = nmod_mat(nr, nc, p)
for j, cv in enumerate(colv):
    for i, v in cv:
        A[i, j] = v
R_, rank = A.rref()
piv, r = [], 0
for c in range(nc):
    if r < rank and int(R_[r, c]) != 0:
        piv.append(c)
        r += 1
del A, R_
print(f"rank {rank} of {nr} rows; {len(piv)} pivot columns ({time.time() - t0:.1f} s)")
I, J, V = [], [], []
for cj, j in enumerate(piv):
    for i, v in colv[j]:
        I.append(i)
        J.append(cj)
        V.append(float(v))
B = sp.csc_matrix((V, (I, J)), shape=(nr, len(piv)))
print(f"pivot block {B.shape}, nnz {B.nnz}; an explicit inverse has {nr * nr} entries and costs {B.nnz * nr} "
      f"multiply-adds to check entry by entry")
for perm in ("NATURAL", "COLAMD", "MMD_AT_PLUS_A", "MMD_ATA"):
    t0 = time.time()
    try:
        lu = spla.splu(B, permc_spec=perm, diag_pivot_thresh=0.1, options={"SymmetricMode": False})
    except Exception as e:
        print(perm, "failed", e)
        continue
    L, U = lu.L.tocsc(), lu.U.tocsr()
    lc = np.diff(L.indptr) - 1
    ur = np.diff(U.indptr)
    cost = int(np.sum(lc.astype(np.int64) * ur.astype(np.int64)))
    print(f"{perm:14s}: nnz(L) {L.nnz:>9d}  nnz(U) {U.nnz:>9d}  total {L.nnz + U.nnz:>9d}  "
          f"check cost {cost:>12d} multiply-adds  ({time.time() - t0:.1f} s)")
