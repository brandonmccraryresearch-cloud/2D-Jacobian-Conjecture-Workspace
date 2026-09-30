import flint
def nullspace_q(rows, ncols):
    """rows: list of lists of fmpq (or ints). Returns list of basis vectors (lists of fmpq) of the right nullspace."""
    if not rows: return [[flint.fmpq(1 if i == j else 0) for i in range(ncols)] for j in range(ncols)]
    A = flint.fmpq_mat(len(rows), ncols, [flint.fmpq(x) for r in rows for x in r])
    R, rank = A.rref()
    piv = []; r = 0
    for c in range(ncols):
        if r < rank and R[r, c] != 0:
            piv.append(c); r += 1
    free = [c for c in range(ncols) if c not in set(piv)]
    basis = []
    for f in free:
        v = [flint.fmpq(0)] * ncols; v[f] = flint.fmpq(1)
        for i, pc in enumerate(piv): v[pc] = -R[i, f]
        basis.append(v)
    return basis
