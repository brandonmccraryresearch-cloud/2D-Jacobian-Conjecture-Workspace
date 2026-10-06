"""chart_small.py -- the m-th top-layer chart system (m odd): alpha = 1 + a_1 u + ... + a_{m-1} u^{m-1} + u^m,
beta = 1 + B_1 u + ... + B_n u^n (n = (3m-1)/2), E5: alpha*beta + u (2 alpha beta' - 3 alpha' beta) = 1.
E_k (k = 1..n) is linear in B_k with coefficient 1 + 2k, which gives B_k(a); the residuals are the coefficients
R_N, N = n+1 .. n+m of E with beta = sum B_k u^k (R_{n+m} vanishes identically since 1 + 2n - 3m = 0)."""
import sympy as sp


def chart_residuals(m):
    n = (3 * m - 1) // 2
    a = sp.symbols(f"a1:{m}")
    A = [sp.Integer(1)] + list(a) + [sp.Integer(1)]
    B = [sp.Integer(1)]
    for k in range(1, n + 1):
        acc = sum((1 + 2 * (k - i) - 3 * i) * A[i] * B[k - i] for i in range(1, min(m, k) + 1))
        B.append(sp.expand(-acc / (1 + 2 * k)))
    R = {}
    for N in range(n + 1, n + m + 1):
        R[N] = sp.expand(sum((1 + 2 * (N - i) - 3 * i) * A[i] * B[N - i] for i in range(0, m + 1) if 0 <= N - i <= n))
    return a, A, B, R


def primitive_generators(m):
    a, A, B, R = chart_residuals(m)
    gens = []
    for N in sorted(R):
        if R[N] == 0:
            continue
        num, den = sp.fraction(sp.together(R[N]))
        P = sp.Poly(num, *a)
        g = sp.gcd_list([int(c) for c in P.coeffs()])
        gens.append((N, sp.expand(num / g), sp.simplify(sp.expand(num / g) / R[N])))
    return a, gens
