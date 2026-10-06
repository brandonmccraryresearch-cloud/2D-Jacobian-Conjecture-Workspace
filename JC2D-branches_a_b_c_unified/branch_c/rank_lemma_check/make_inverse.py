"""make_inverse.py -- the certificate checked by the Lean kernel: C = M_S^{-1} mod p for the pivot block M_S of M_W.

1. Pivot columns of M_W mod p (FLINT rref, first pivot in each row, as step3b_rank_lift.pivot_cols).  Full row rank
   is required: one pivot per row.
2. M_S = the square block of the pivot columns; C = M_S^{-1} mod p (FLINT); C * M_S = I is checked here (FLINT).
3. Statistics that bear on the choice of certificate: density of C, column and row supports of M_S, and the
   block-triangular form of M_S (Dulmage-Mendelsohn; needs scipy, skipped without it).
Output: a pickle {"p", "piv", "pivcols", "colv", "C"}: colv = the pivot columns' entries, C = numpy int64 array.
usage: python3 make_inverse.py MATRIX.pkl OUT.pkl      (needs python-flint, numpy)
"""
import sys, pickle, time, hashlib
import numpy as np
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
print(f"rank {rank} of {nr} rows ({'FULL ROW RANK' if rank == nr else 'NOT full row rank'}); {len(piv)} pivot "
      f"columns; sha256 of the pivot list {hashlib.sha256(repr(piv).encode()).hexdigest()[:16]} "
      f"({time.time() - t0:.1f} s)", flush=True)
assert rank == nr == len(piv), "M_W does not have full row rank mod p"
n = nr
MS = nmod_mat(n, n, p)
for jj, j in enumerate(piv):
    for i, v in colv[j]:
        MS[i, jj] = v
t1 = time.time()
Cinv = MS.inv()
print(f"C = M_S^(-1) mod {p}: {time.time() - t1:.1f} s", flush=True)
t1 = time.time()
prod = Cinv * MS
ok = all(int(prod[i, k]) == (1 if i == k else 0) for i in range(n) for k in range(n))
print(f"C * M_S == I (FLINT): {ok} ({time.time() - t1:.1f} s)", flush=True)
assert ok
del prod
C = np.array([[int(Cinv[i, k]) for k in range(n)] for i in range(n)], dtype=np.int64)
print(f"C: {np.count_nonzero(C)} nonzero entries of {n * n} ({np.count_nonzero(C) / n / n:.1%}); "
      f"sha256 {hashlib.sha256(C.tobytes()).hexdigest()[:16]}")
sup = [len(colv[j]) for j in piv]
rowcnt = np.zeros(n, dtype=int)
for j in piv:
    for i, _ in colv[j]:
        rowcnt[i] += 1
print(f"M_S: {sum(sup)} nonzero entries; column supports {min(sup)}..{max(sup)}; row supports "
      f"{rowcnt.min()}..{rowcnt.max()}")
try:
    import scipy.sparse as sp
    from scipy.sparse.csgraph import maximum_bipartite_matching, connected_components
    I_, J_ = [], []
    for jj, j in enumerate(piv):
        for i, _ in colv[j]:
            I_.append(i)
            J_.append(jj)
    B = sp.csr_matrix((np.ones(len(I_)), (I_, J_)), shape=(n, n))
    match = maximum_bipartite_matching(B, perm_type="column")
    assert (match >= 0).all()
    ncomp, lab = connected_components((B[:, match] != 0).astype(int), directed=True, connection="strong")
    sizes = np.bincount(lab)
    print(f"block-triangular form of M_S: {ncomp} diagonal blocks, the largest of size {sizes.max()} "
          f"({int((sizes == 1).sum())} of size 1)")
except ImportError:
    print("scipy not available: block-triangular statistics skipped")
pickle.dump({"p": p, "piv": piv, "pivcols": [cols[j] for j in piv], "colv": [colv[j] for j in piv], "C": C},
            open(sys.argv[2], "wb"))
print(f"total {time.time() - t0:.1f} s")
