"""Certificates  target = sum_i c_i * G_i  over K5 = Q[w]/(R), found by linear algebra over Q with w as a variable.
Polynomials: dict {exponent tuple: fmpq_poly (in w, reduced mod R)}.  Unknowns: the rational coordinates
(basis 1,w,..,w^4) of the coefficients of c_i on all monomials of total degree <= D_i."""
import itertools, sys, time
from flint import fmpq_poly, fmpq, nmod_mat, fmpq_mat, fmpz
sys.set_int_max_str_digits(0)
Rr = fmpq_poly([26, 0, 3, 3, -1, 1]); Z = fmpq_poly([0])
WPOW = [(fmpq_poly([0] * j + [1])) % Rr for j in range(5)]   # w^j (trivially reduced)
def monos(n, D):
    out = []
    for d in range(D + 1):
        for c in itertools.combinations_with_replacement(range(n), d):
            e = [0] * n
            for i in c: e[i] += 1
            out.append(tuple(e))
    return out
def columns(gens, degs, n):
    """column list: (i, m, j) meaning the unknown coefficient of w^j * x^m in c_i."""
    cols = []
    for i, D in enumerate(degs):
        for m in monos(n, D):
            for j in range(5): cols.append((i, m, j))
    return cols
def column_poly(g, m, j):
    """w^j x^m g as dict {(M, k): fmpq} with k the w-power after reduction mod R."""
    out = {}
    for mm, c in g.items():
        prod = (c * WPOW[j]) % Rr
        M = tuple(a + b for a, b in zip(mm, m))
        for k, v in enumerate(list(prod)):
            if v != 0: out[(M, k)] = v
    return out
def build(gens, degs, target, n):
    cols = columns(gens, degs, n)
    colpolys = [column_poly(gens[i], m, j) for (i, m, j) in cols]
    rows = sorted(set(k for cp in colpolys for k in cp) | set((M, k) for M, c in target.items() for k in range(5) if k < len(list(c)) and list(c)[k] != 0))
    ridx = {r: a for a, r in enumerate(rows)}
    rhs = {}
    for M, c in target.items():
        for k, v in enumerate(list(c)):
            if v != 0: rhs[ridx[(M, k)]] = v
    return cols, colpolys, rows, ridx, rhs
def modp_consistent(cols, colpolys, rows, ridx, rhs, p):
    A = nmod_mat(len(rows), len(cols) + 1, p)
    def red(v):
        v = fmpq(v); return int(v.p) % p * pow(int(v.q) % p, p - 2, p) % p
    for c, cp in enumerate(colpolys):
        for key, v in cp.items(): A[ridx[key], c] = red(v)
    for r, v in rhs.items(): A[r, len(cols)] = red(v)
    Aonly = nmod_mat(len(rows), len(cols), p)
    for c, cp in enumerate(colpolys):
        for key, v in cp.items(): Aonly[ridx[key], c] = red(v)
    return Aonly.rank(), A.rank()
