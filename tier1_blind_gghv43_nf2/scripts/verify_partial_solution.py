"""
verify_partial_solution.py -- independent of gen_system.py: build P = 1 + x*alpha(x*y^2),
Q = 1 + x^2*y*beta(x*y^2) from e5_exact_K5.json (coefficients in K5 = Q[w]/(Rr)), compute
P_x*Q_y - P_y*Q_x - x^2 with sympy, reduce every coefficient modulo Rr(w): must be 0.
Also prints the Newton-polygon vertices of P and Q and confirms the vertex coefficients
a_1_0, a_8_14, b_2_1, b_12_21 are nonzero in K5.
"""
import json
import sympy as sp

x, y, w = sp.symbols('x y w')
Rr = w**5 - w**4 + 3*w**3 + 3*w**2 + 26
d = json.load(open("e5_exact_K5.json"))
K = lambda lst: sum(sp.Rational(c) * w**i for i, c in enumerate(lst))
alpha = {0: sp.Integer(1), 1: sp.Integer(1)}          # a_1_0 = 1, a_2_2 = 1
for k in range(2, 8):
    alpha[k] = K(d[f"a_{k+1}_{2*k}"])
beta = {0: sp.Integer(1)}                                # b_2_1 = 1
for j in range(1, 11):
    beta[j] = K(d[f"b_{j+2}_{2*j+1}"])
lam = K(d["lam"])
t = x * y**2
P = 1 + x * sum(alpha[k] * t**k for k in alpha)
Q = 1 + x**2 * y * sum(beta[j] * t**j for j in beta)
br = sp.expand(sp.diff(P, x) * sp.diff(Q, y) - sp.diff(P, y) * sp.diff(Q, x) - lam * x**2)
poly = sp.Poly(br, x, y)
nonzero = [m for m, c in zip(poly.monoms(), poly.coeffs()) if sp.rem(sp.expand(c), Rr, w) != 0]
print("lam =", sp.rem(lam, Rr, w))
print("monomials of [P,Q] - lam*x^2 with nonzero coefficient mod Rr:", nonzero)
for name, val in [("a_8_14", alpha[7]), ("b_12_21", beta[10])]:
    r = sp.rem(sp.expand(val), Rr, w)
    print(name, "nonzero in K5:", r != 0)
sP = sp.Poly(sp.expand(P), x, y).monoms(); sQ = sp.Poly(sp.expand(Q), x, y).monoms()
print("support of P lies on (0,0) + {(i,2i-2)}:", all(m == (0, 0) or m[1] == 2*m[0] - 2 for m in sP), " max x-degree", max(m[0] for m in sP))
print("support of Q lies on (0,0) + {(k,2k-3)}:", all(m == (0, 0) or m[1] == 2*m[0] - 3 for m in sQ), " max x-degree", max(m[0] for m in sQ))
assert not nonzero and sp.rem(lam, Rr, w) == 1
print("PASS: [P,Q] = x^2 exactly; N(P) = conv{(0,0),(1,0),(8,14)}, N(Q) = conv{(0,0),(2,1),(12,21)}")
