# Exact data for stages 3-4: theta-chart shape lemma, normalization, Lean-slice polynomials.
import flint, json, sympy as sp, re, pickle
from k5 import K5, lean_point, Rp
from cp_common import *
from yform import S_list
S = S_list(16)
st2 = json.load(open('stage2.json'))
G = {n: sp.sympify(e, locals={f'y{i}': Y[i-1] for i in range(1, 8)}) for n, e in st2['G'].items()}
# --- univariate helpers (flint fmpq_poly <-> sympy) ---
X = flint.fmpq_poly([0, 1])
def fp(expr, var):   # sympy univariate -> fmpq_poly
    P = sp.Poly(sp.expand(expr), var); cs = P.all_coeffs()[::-1]
    return flint.fmpq_poly([flint.fmpq(int(sp.Rational(c).p), int(sp.Rational(c).q)) for c in cs])
def sp_(p, var):     # fmpq_poly -> sympy
    return sum(sp.Rational(int(p[i].p), int(p[i].q)) * var ** i for i in range(p.degree() + 1)) if p.degree() >= 0 else sp.Integer(0)
def compose(p, q):   # p(q(x))
    r = flint.fmpq_poly([]); 
    for i in range(p.degree(), -1, -1): r = r * q + p[i]
    return r
def invmod(p, m):
    g, a, b = p.xgcd(m); assert g.degree() == 0; return a / g[0]
# --- Lean point, theta data ---
P = lean_point(); a7 = P['a7']; y7v = a7.inv()
Yv = [P[f'a{7-i}'] * y7v for i in range(1, 7)] + [y7v]
th2 = Yv[1] / (Yv[0] ** 2)
def as_poly_in(x, base):
    cols = [(base ** k).coeffs() for k in range(5)]
    Am = flint.fmpq_mat(5, 5, [cols[k][i] for i in range(5) for k in range(5)])
    sol = Am.solve(flint.fmpq_mat(5, 1, x.coeffs()))
    return flint.fmpq_poly([sol[k, 0] for k in range(5)])
# G5a, G6a in (t, s): dehomogenize y1 = 1, y2 = t, y3 = s
G5a = sp.expand(G['g5a'].subs({Y[0]: 1, Y[1]: t, Y[2]: s}))
G6a = sp.expand(G['g6a'].subs({Y[0]: 1, Y[1]: t, Y[2]: s}))
# G5a = (t - c) s - N(t)
cs_ = sp.Poly(G5a, s).all_coeffs()   # [coef of s, const]
assert len(cs_) == 2
lead5 = sp.expand(cs_[0]); N5 = sp.expand(-cs_[1])
c = sp.solve(lead5, t)[0]; assert sp.expand(lead5 - (t - c)) == 0
cs6 = sp.Poly(G6a, s).all_coeffs(); assert len(cs6) == 3 and cs6[0] == 1
e6 = -cs6[1]; G6a0 = cs6[2]
Res = sp.expand((t - c) ** 2 * G6a0 + N5 ** 2 - e6 * N5 * (t - c))
# Sylvester identity: Res = (t-c)^2*G6a - ((t-c)*s + N - e*(t-c))*G5a
assert sp.expand(Res - ((t - c) ** 2 * G6a - ((t - c) * s + N5 - e6 * (t - c)) * G5a)) == 0
ResP = fp(Res, t); kappa = ResP[ResP.degree()]
m = ResP / kappa
m_expected = None
print("deg Res:", ResP.degree(), " m irreducible:", len(m.factor()[1]) == 1 and m.factor()[1][0][1] == 1)
# check th2 is a root of m (evaluate m at th2 in K5)
val = K5(0)
for i in range(m.degree(), -1, -1): val = val * th2 + K5(flint.fmpq_poly([m[i]]))
print("m(theta2) = 0 at Lean point:", val.is_zero())
mS = sp_(m, t)
# s = q3(t): (t - c)^{-1} * N(t) mod m
invc = invmod(fp(t - c, t), m)
q = {2: X}
q[3] = (invc * fp(N5, t)) % m
Hs = {}
for i, n in [(4, 'g4'), (5, 'g5b'), (6, 'g6b'), (7, 'g7')]:
    H = sp.expand(Y[i-1] - G[n])          # g_i = y_i - H_i(y1,y2,y3)
    assert all(v in (Y[0], Y[1], Y[2]) for v in H.free_symbols), (n, H.free_symbols)
    Hs[i] = H
    Hts = sp.expand(H.subs({Y[0]: 1, Y[1]: t, Y[2]: s}))
    q[i] = compose(fp(Hts.subs(s, 0), t), X)  # placeholder; recompute properly below
    # proper: substitute s = q3(t) as polynomial composition in two variables
    Hp = sp.Poly(Hts, s); acc = flint.fmpq_poly([])
    for (ks,), cf in Hp.terms():
        acc += fp(cf, t) * (q[3] ** ks)
    q[i] = acc % m
# sanity vs Lean point: theta_i = y_i / y1^i
for i in range(2, 8):
    lhs = Yv[i-1] / (Yv[0] ** i); qi = q[i]
    val = K5(0)
    for j in range(qi.degree(), -1, -1): val = val * th2 + K5(flint.fmpq_poly([qi[j]]))
    assert (val - lhs).is_zero(), i
print("theta_i = q_i(theta2) verified at Lean point for i=2..7")
# sigma(t) = S10(1, t, q3, ..., q7) mod m
S10 = S[10]
Pp = sp.Poly(S10, *Y); sig = flint.fmpq_poly([])
qq = [flint.fmpq_poly([1])] + [q[i] for i in range(2, 8)]
for mon, cf in Pp.terms():
    term = flint.fmpq_poly([flint.fmpq(int(sp.Rational(cf).p), int(sp.Rational(cf).q))])
    for i, e in enumerate(mon):
        if e: term = (term * qq[i] ** e) % m
    sig += term
sig = sig % m
I3 = invmod((q[7] ** 3) % m, m)
Ups = {1: (sig * sig * I3) % m}
for i in range(2, 8): Ups[i] = (Ups[1] ** i * q[i]) % m
for i in range(1, 8):
    val = K5(0)
    for j in range(Ups[i].degree(), -1, -1): val = val * th2 + K5(flint.fmpq_poly([Ups[i][j]]))
    assert (val - Yv[i-1]).is_zero(), i
print("Upsilon_i(theta2) = Lean-slice y_i verified for i=1..7 (normalization S10^2 = y7^3 reproduces the Lean slice)")
omega = as_poly_in(K5(flint.fmpq_poly([0, 1])), th2)
Rpoly = flint.fmpq_poly([26, 0, 3, 3, -1, 1])
print("R(omega(t)) = 0 mod m:", (compose(Rpoly, omega) % m).degree() < 0)
Yw = {i: flint.fmpq_poly(Yv[i-1].coeffs()) for i in range(1, 8)}
for i in range(1, 8):
    assert ((compose(Yw[i], omega) - Ups[i]) % m).degree() < 0
print("Y_i(omega(t)) = Upsilon_i(t) mod m verified")
data = {'c': str(c), 'N5': str(N5), 'e6': str(e6), 'G6a0': str(G6a0), 'kappa': str(kappa), 'm': str(sp_(m, t)),
        'invc': str(sp_(invc, t)), 'q': {i: str(sp_(q[i], t)) for i in q}, 'H': {i: str(Hs[i]) for i in Hs},
        'sigma': str(sp_(sig, t)), 'I3': str(sp_(I3, t)), 'Ups': {i: str(sp_(Ups[i], t)) for i in Ups},
        'omega': str(sp_(omega, t)), 'Yw': {i: str(sp_(Yw[i], w)) for i in Yw}}
json.dump(data, open('stage3data.json', 'w'))
print("sizes: m", m.degree(), "max digits in Ups:", max(len(str(Ups[i])) for i in Ups))
