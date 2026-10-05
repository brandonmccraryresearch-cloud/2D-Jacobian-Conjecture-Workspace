"""k5.py -- exact arithmetic in K5 = Q[w]/(R), R = w^5 - w^4 + 3w^3 + 3w^2 + 26, and linear algebra over K5.
Elements are tuples of 5 flint.fmpq (coefficients of 1, w, w^2, w^3, w^4).  w^5 = w^4 - 3w^3 - 3w^2 - 26."""
import flint

Z = flint.fmpq(0)
ONE = flint.fmpq(1)


def k5(c0=0, c1=0, c2=0, c3=0, c4=0):
    return tuple(flint.fmpq(c) if not isinstance(c, flint.fmpq) else c for c in (c0, c1, c2, c3, c4))


ZERO5 = k5()
ONE5 = k5(1)
W5 = k5(0, 1)


def iszero(a):
    return all(c == 0 for c in a)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def neg(a):
    return tuple(-x for x in a)


def smul(s, a):
    return tuple(s * x for x in a)


def mul(a, b):
    c = [Z] * 9
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            if y != 0:
                c[i + j] += x * y
    for k in range(8, 4, -1):          # w^k = w^(k-5) * (w^4 - 3w^3 - 3w^2 - 26)
        t = c[k]
        if t != 0:
            c[k - 1] += t
            c[k - 2] -= 3 * t
            c[k - 3] -= 3 * t
            c[k - 5] -= 26 * t
            c[k] = Z
    return tuple(c[:5])


def regmat(a):
    """5x5 rational matrix of multiplication by a in the basis 1, w, ..., w^4 (column j = a * w^j)."""
    cols = []
    b = ONE5
    for j in range(5):
        cols.append(mul(a, b))
        b = mul(b, W5)
    return flint.fmpq_mat(5, 5, [cols[j][i] for i in range(5) for j in range(5)])


def inv(a):
    assert not iszero(a), "division by zero in K5"
    x = regmat(a).solve(flint.fmpq_mat(5, 1, [1, 0, 0, 0, 0]))
    r = tuple(x[i, 0] for i in range(5))
    assert mul(a, r) == ONE5
    return r


def div(a, b):
    return mul(a, inv(b))


def height_digits(a):
    return max([len(str(abs(int(c.p)))) for c in a] + [len(str(int(c.q))) for c in a])


def to_str(a):
    return "[" + ",".join(str(c) for c in a) + "]"


def from_strs(lst):
    return tuple(flint.fmpq(*map(int, s.split("/"))) if "/" in s else flint.fmpq(int(s)) for s in lst)


# ---------------- linear algebra over K5 (dense, Gaussian elimination) ----------------

def rref(M, ncols=None):
    """Row-reduce a list of rows (lists of K5).  Returns (R, pivots): R in reduced row echelon form."""
    M = [list(r) for r in M]
    if not M:
        return M, []
    ncols = len(M[0]) if ncols is None else ncols
    piv, r = [], 0
    for c in range(ncols):
        p = next((i for i in range(r, len(M)) if not iszero(M[i][c])), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        iv = inv(M[r][c])
        M[r] = [mul(iv, x) for x in M[r]]
        for i in range(len(M)):
            if i != r and not iszero(M[i][c]):
                f = M[i][c]
                M[i] = [sub(x, mul(f, y)) for x, y in zip(M[i], M[r])]
        piv.append(c)
        r += 1
        if r == len(M):
            break
    return M, piv


def rank(M):
    return len(rref(M)[1])


def kernel(M, n):
    """Basis of {x in K5^n : M x = 0} (right kernel), as list of vectors."""
    if not M:
        return [[ONE5 if i == j else ZERO5 for i in range(n)] for j in range(n)]
    R, piv = rref(M, n)
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        v = [ZERO5] * n
        v[f] = ONE5
        for i, pc in enumerate(piv):
            v[pc] = neg(R[i][f])
        basis.append(v)
    return basis


def transpose(M, ncols):
    return [[M[i][j] for i in range(len(M))] for j in range(ncols)]


def left_kernel(M, ncols):
    """Basis of {y : y^T M = 0}."""
    return kernel(transpose(M, ncols), len(M))


def matvec(M, v):
    out = []
    for row in M:
        s = ZERO5
        for x, y in zip(row, v):
            if not iszero(x) and not iszero(y):
                s = add(s, mul(x, y))
        out.append(s)
    return out


def solve_square(M, b):
    """Solve M x = b for invertible square M (list of rows)."""
    n = len(M)
    aug = [list(M[i]) + [b[i]] for i in range(n)]
    R, piv = rref(aug, n)
    assert piv == list(range(n)), "matrix not invertible"
    return [R[i][n] for i in range(n)]


def inverse(M):
    n = len(M)
    aug = [list(M[i]) + [ONE5 if i == j else ZERO5 for j in range(n)] for i in range(n)]
    R, piv = rref(aug, n)
    assert piv == list(range(n)), "matrix not invertible"
    return [R[i][n:] for i in range(n)]
