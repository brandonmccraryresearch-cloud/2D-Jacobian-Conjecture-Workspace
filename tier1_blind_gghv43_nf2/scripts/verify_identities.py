"""
verify_identities.py -- exact symbolic checks (sympy) of every hand-derived identity used in the
written argument.  Nothing here is numerical.
 (I1) The weight -4 block produced by gen_system equals, coefficient by coefficient, the
      expansion of  [x*alpha(t), x^2*y*beta(t)] - lam*x^2  with t = x*y^2,
      alpha_k = a_{k+1,2k}, beta_j = b_{j+2,2j+1}, and
      [x*alpha(t), x^2*y*beta(t)] = x^2 * E(t),  E = alpha*beta + 2t*alpha*beta' - 3t*alpha'*beta.
 (I2) The x^2 equation reads a_1_0*b_2_1 - lam = 0  (so lam != 0  <=> a_1_0*b_2_1 != 0).
 (I3) (t*beta^2/alpha^3)' = beta*E/alpha^4   (generic polynomials).
 (I4) Normalisation: the log-weight matrix of (P-scale, Q-scale, x-scale, y-scale) on
      a_1_0, b_2_1, a_8_14 has rank 3; residual action of the torus fixing them multiplies
      a_{ij} by Y^{j-2i+2} and b_{kl} by Y^{l-2k+3} (times 7th roots of unity in x).
 (I5) The GGHV map phi(x)=1/x, phi(y)=x^4*y has Jacobian -x^2 and sends the cases a),b) polygons
      {(-1,0),(0,0),2(28,8),2(24,7)}, {(2,1),(0,0),3(28,8),3(24,7)} to the brief's polygons.
"""
import sympy as sp
from gen_system import build

x, y, t, lam = sp.symbols('x y t lam')
LP, LQ, eqs, tgt = build()
w = lambda ij: ij[1] - 2 * ij[0]

# (I1)
al = {k: sp.Symbol(f"a_{k+1}_{2*k}") for k in range(8)}
be = {j: sp.Symbol(f"b_{j+2}_{2*j+1}") for j in range(11)}
alpha = sum(al[k] * t**k for k in range(8))
beta = sum(be[j] * t**j for j in range(11))
P2 = x * alpha.subs(t, x * y**2)
Q3 = x**2 * y * beta.subs(t, x * y**2)
br = sp.expand(sp.diff(P2, x) * sp.diff(Q3, y) - sp.diff(P2, y) * sp.diff(Q3, x))
E = sp.expand(alpha * beta + 2 * t * alpha * sp.diff(beta, t) - 3 * t * sp.diff(alpha, t) * beta)
assert sp.expand(br - x**2 * E.subs(t, x * y**2)) == 0
print("(I1a) [x*alpha(t), x^2*y*beta(t)] = x^2*E(t): OK")
lhs = sp.Poly(br - lam * x**2, x, y)
gen = {}
for k in eqs:
    if w(k) != -4:
        continue
    s = sum(c * sp.Symbol(pv) * sp.Symbol(qv) for c, pv, qv in eqs[k]) - (lam if k == tgt else 0)
    gen[k] = sp.expand(s)
mons = {m: sp.expand(c) for m, c in zip(lhs.monoms(), lhs.coeffs())}
assert set(mons) == set(gen), (sorted(set(mons) ^ set(gen)))
assert all(sp.expand(mons[m] - gen[m]) == 0 for m in gen)
print("(I1b) weight -4 block of generator == coefficients of [P_-2,Q_-3]-lam*x^2:", len(gen), "equations, OK")
# (I2)
s2 = sum(c * sp.Symbol(pv) * sp.Symbol(qv) for c, pv, qv in eqs[tgt]) - lam
assert sp.expand(s2 - (sp.Symbol('a_1_0') * sp.Symbol('b_2_1') - lam)) == 0
print("(I2) x^2-equation: a_1_0*b_2_1 - lam = 0: OK")
# (I3)
A = sum(sp.Symbol(f"A{i}") * t**i for i in range(8))
B = sum(sp.Symbol(f"B{i}") * t**i for i in range(11))
EE = A * B + 2 * t * A * sp.diff(B, t) - 3 * t * sp.diff(A, t) * B
assert sp.simplify(sp.diff(t * B**2 / A**3, t) - B * EE / A**4) == 0
print("(I3) (t*beta^2/alpha^3)' = beta*E/alpha^4: OK")
# (I4)
M = sp.Matrix([[1, 0, 1, 0], [0, 1, 2, 1], [1, 0, 8, 14]])
assert M.rank() == 3
X, Y, sP, sQ = sp.symbols('X Y sP sQ', positive=True)
sol = {sP: Y**2, sQ: Y**3, X: Y**-2}
for (i, j) in [(1, 0), (8, 14)]:
    assert sp.simplify((sP * X**i * Y**j).subs(sol)) == 1
assert sp.simplify((sQ * X**2 * Y**1).subs(sol)) == 1
for (i, j) in LP:
    assert sp.simplify((sP * X**i * Y**j).subs(sol) - Y**(j - 2 * i + 2)) == 0
for (k, l) in LQ:
    assert sp.simplify((sQ * X**k * Y**l).subs(sol) - Y**(l - 2 * k + 3)) == 0
print("(I4) normalisation rank 3; residual Y-weights w+2 (P), w+3 (Q): OK")
# (I5)
phi = lambda ij: (4 * ij[1] - ij[0], ij[1])      # phi(x^a y^b) = x^{4b-a} y^b
NP0 = [(-1, 0), (0, 0), (56, 16), (48, 14)]
NQ0 = [(2, 1), (0, 0), (84, 24), (72, 21)]
assert sorted(map(phi, NP0)) == sorted([(0, 0), (1, 0), (8, 14), (8, 16)])
assert sorted(map(phi, NQ0)) == sorted([(0, 0), (2, 1), (12, 21), (12, 24)])
fx, fy = 1 / x, x**4 * y
assert sp.simplify(sp.diff(fx, x) * sp.diff(fy, y) - sp.diff(fx, y) * sp.diff(fy, x) + x**2) == 0
print("(I5) phi maps GGHV cases a),b) polygons to the brief's polygons; Jac(phi) = -x^2: OK")
