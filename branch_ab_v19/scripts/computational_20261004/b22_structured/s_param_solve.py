"""Solve in s-parametrization: a7=s^2, c_10=s^3, constrain |s|>0.1 to avoid degeneracy."""
import json, sympy as sp
import numpy as np
from scipy.optimize import differential_evolution

data = json.load(open('/tmp/c_poly.json'))
a = sp.symbols('a1:8')  # a1..a7
s = sp.Symbol('s')
c = {int(n): sp.sympify(expr) for n, expr in data.items()}

# Substitute a7 -> s^2
c_sub = {}
for n in range(10, 17):
    c_sub[n] = sp.expand(c[n].subs(a[6], s**2))

# Equations: c_11..c_16 = 0, c_10 - s^3 = 0, in (a1..a6, s)
a16 = a[:6]
eqs = [c_sub[n] for n in range(11, 17)] + [c_sub[10] - s**3]
print(f"{len(eqs)} equations in (a1..a6, s)")

f = sp.lambdify(a16 + (s,), eqs, 'numpy')

def obj(x):
    # x: 14 reals -> 7 complex (a1..a6, s)
    xc = x[:7] + 1j*x[7:]
    # penalize small |s|
    if abs(xc[6]) < 0.05:
        return 1e6
    r = f(*xc)
    return sum(abs(v)**2 for v in r) + 1e6*max(0, 0.05-abs(xc[6]))**2

bounds = [(-3, 3)]*14
result = differential_evolution(obj, bounds, maxiter=500, seed=1, tol=1e-12,
                                workers=1, updating='deferred', polish=True)
print(f"fun={result.fun:.3e}")
if result.fun < 1e-10:
    x = result.x
    xc = x[:7] + 1j*x[7:]
    a7v = xc[6]**2
    print(f"s={xc[6]}, |s|={abs(xc[6]):.4f}")
    print(f"a7=s^2={a7v}")
    sol = list(xc[:6]) + [a7v]
    # verify torus: a7^3 * b0^2 = 1 where b0=1/c10, c10=s^3
    b0 = 1/xc[6]**3
    print(f"|a7^3*b0^2| = {abs(a7v**3 * b0**2):.6f} (should be 1.0)")
    json.dump({'a': [[v.real, v.imag] for v in sol], 's': [xc[6].real, xc[6].imag]},
              open('/tmp/s_sol.json', 'w'))
    print("saved")
    for i, v in enumerate(sol, 1):
        print(f"  a{i} = {v}")
else:
    print("not converged")
