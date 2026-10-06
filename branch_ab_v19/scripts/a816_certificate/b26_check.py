"""Independent checks of CAIC's B2.6 (m=5) claims that need no system: T(a4) = 9a^10 + 37200a^5 + 95051008."""
import sympy as sp
a, u = sp.symbols("a u")
T = 9*a**10 + 37200*a**5 + 95051008
f = 9*u**2 + 37200*u + 95051008                 # T = f(a^5)
print("factor_list(T) over Q:", sp.factor_list(T))
print("disc_u(f) (quadratic in u = a^5):", sp.discriminant(f, u))
print("disc_a(T) (degree-10 polynomial):", sp.discriminant(T, a))
print("real roots of T:", sp.real_roots(T))
print("content / leading coeff:", sp.Poly(T, a).content(), sp.Poly(T, a).LC())
# irreducibility over Q independent of sympy: Capelli -> f irreducible and the root alpha of f is not a 5th power in Q(alpha)
print("f irreducible:", sp.Poly(f, u).is_irreducible)
# reduction test: T mod small primes (a factorization mod p into an irreducible of degree 10 proves irreducibility over Q)
for p in [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]:
    Tp = sp.Poly(T, a, modulus=p)
    if Tp.degree() == 10:
        degs = sorted(sp.degree(g[0], a) for g in Tp.factor_list()[1] for _ in range(g[1]))
        if degs == [10]:
            print(f"T irreducible mod {p} (degree 10 kept) -> irreducible over Q"); break
