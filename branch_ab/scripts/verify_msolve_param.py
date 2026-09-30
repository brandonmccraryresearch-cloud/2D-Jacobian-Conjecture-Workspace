# Attribution: computed by the referee (Claude/Anthropic, Tier 1 agent) during Round 6 review.
# Part of the characteristic-0 verification for the branch-(a,b) elimination.

"""Exact verification over Q[t]/(W) of the paper's imported msolve parametrization (e5_m7.out):
a_i = -v_i(t)/(c_i W'(t)), a6 = t; every polynomial of the msolve input e5_m7.ms must vanish mod W.
Also checks the msolve input equals (rational multiple of) my reduced top-layer system C_11..C_16."""
import re, sys, sympy as sp
from flint import fmpq_poly, fmpq
S = sys.argv[1] if len(sys.argv) > 1 else '.'
data = eval(re.sub(r'(\d+)\^(\d+)', r'(\1**\2)', open(f'{S}/e5_m7.out').read().strip().rstrip(':')))
pl = data[1][5][1]
W = fmpq_poly(pl[0][1]); Wd = fmpq_poly(pl[1][1])
print("deg W =", W.degree(), "| stated W' is the derivative of W:", Wd == W.derivative())
g, Winv, _ = Wd.xgcd(W); assert g == 1
A = {f"a{i+1}": (-fmpq_poly(it[0][1]) * Winv / it[1]) % W for i, it in enumerate(pl[2])}
A["a6"] = fmpq_poly([0, 1])
lines = open(f'{S}/e5_m7.ms').read().strip().split('\n')
vars_ = lines[0].split(','); polys = "\n".join(lines[2:]).split(',\n'); syms = sp.symbols(vars_)
bad = 0
for P in polys:
    poly = sp.Poly(sp.sympify(P.replace('^', '**')), *syms); acc = fmpq_poly([0])
    for mon, coef in zip(poly.monoms(), poly.coeffs()):
        term = fmpq_poly([int(coef)])
        for vn, e in zip(vars_, mon):
            for _ in range(e): term = (term * A[vn]) % W
        acc = (acc + term) % W
    bad += (acc != 0)
print(f"msolve input polynomials NOT vanishing on the parametrization (exact mod W over Q): {bad} of {len(polys)}")
a = sp.symbols('a1:7'); Al = [sp.Integer(1)] + list(a) + [sp.Integer(1)]; B = [sp.Integer(1)]
for k in range(1, 11):
    B.append(sp.expand(-sum((1 + 2*(k-i) - 3*i) * Al[i] * B[k-i] for i in range(1, min(k, 7) + 1)) / (1 + 2*k)))
mine = [sp.expand(sum((1 + 2*(k-i) - 3*i) * Al[i] * B[k-i] for i in range(8) if 0 <= k-i <= 10)) for k in range(11, 17)]
theirs = [sp.expand(sp.sympify(P.replace('^', '**')).subs({sp.Symbol(f'a{i}'): a[i-1] for i in range(1, 7)})) for P in polys]
print("msolve input = r * C_k (top layer, alpha0=beta0=alpha7=1):", [(k, sp.cancel(t / m)) for k, (t, m) in enumerate(zip(theirs, mine), 11)])
