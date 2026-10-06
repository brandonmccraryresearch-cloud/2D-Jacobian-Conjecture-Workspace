"""Independent verification of B2.6 back-substitution."""
import sympy as sp
a1, a2, a3, a4 = sp.symbols('a1 a2 a3 a4')
T = 9*a4**10 + 37200*a4**5 + 95051008

# 1. Determinant of the linear system
M = sp.Matrix([
    [0, 91, -72*a4],
    [416, -99*a4, 12*a4**2],
    [-10*a4, a4**2, 0]
])
det = sp.factor(M.det())
print(f"det(M) = {det}")
print(f"Claim 30408*a4^3: {det == 30408*a4**3}")

# 2. Solve and check formulas
rhs = sp.Matrix([-21*a4**3, 0, -182])
sol = M.LUsolve(rhs)
f1 = sp.simplify(sol[0] - (3*a4**5+13078)/(362*a4))
f2 = sp.simplify(sol[1] - 3*(5*a4**5+10816)/(181*a4**2))
f3 = sp.simplify(sol[2] - 7*(123*a4**5+70304)/(2172*a4**3))
print(f"\nFormula a1 correct: {f1 == 0}")
print(f"Formula a2 correct: {f2 == 0}")
print(f"Formula a3 correct: {f3 == 0}")

# 3. T(0) != 0
print(f"\nT(0) = {T.subs(a4, 0)} (nonzero: {T.subs(a4,0) != 0})")

# 4. All 10 GB elements vanish mod T
gb = [
    48*a3**2 - 133*a2*a4 + 448*a1,
    2*a2*a3 - 7*a1*a4 + 105,
    21*a2**2 - 32*a1*a3 + 56*a4,
    7*a1*a2 - 21*a4**2 + 24*a3,
    224*a1**2 - 36*a3*a4 - 679*a2,
    21*a4**3 - 72*a3*a4 + 91*a2,
    12*a3*a4**2 - 99*a2*a4 + 416*a1,
    a2*a4**2 - 10*a1*a4 + 182,
    63*a1*a4**2 - 208*a1*a3 + 427*a4,
    a1*a3*a4 - 49*a4**2 + 117*a3,
]
A1 = (3*a4**5+13078)/(362*a4)
A2 = 3*(5*a4**5+10816)/(181*a4**2)
A3 = 7*(123*a4**5+70304)/(2172*a4**3)
TP = sp.Poly(T, a4)
ok = True
for i, p in enumerate(gb):
    v = sp.expand(p.subs({a1: A1, a2: A2, a3: A3}))
    num, den = sp.together(v).as_numer_denom()
    # den is c*a4^k; a4 invertible mod T since T(0)!=0
    r = sp.rem(sp.Poly(num, a4), TP)
    if r.as_expr() != 0:
        print(f"GB[{i}] FAILS: remainder {r.as_expr()}")
        ok = False
print(f"\nAll 10 GB vanish mod T: {ok}")

# 5. Residuals r0..r3 vanish mod T (from the Singular script)
r0 = 512*a1**5*a3 - 896*a1**4*a2**2 - 1792*a1**4*a4 + 2624*a1**3*a2*a3 + 4032*a1**3 + 2128*a1**2*a2**3 - 3136*a1**2*a2*a4 - 4016*a1**2*a3**2 - 6536*a1*a2**2*a3 + 5208*a1*a2 + 13572*a1*a3*a4 - 539*a2**4 + 4389*a2**2*a4 + 5256*a2*a3**2 - 19812*a3 - 11011*a4**2
r1 = 384*a1**4*a2*a3 - 672*a1**3*a2**3 - 1344*a1**3*a2*a4 - 256*a1**3*a3**2 + 2752*a1**2*a2**2*a3 + 3024*a1**2*a2 + 792*a1**2*a3*a4 + 1008*a1*a2**4 - 3346*a1*a2**2*a4 - 4912*a1*a2*a3**2 - 872*a1*a3 + 364*a1*a4**2 - 2648*a2**3*a3 + 4550*a2**2 + 12596*a2*a3*a4 + 2112*a3**3 - 25844*a4
r2 = 256*a1**4*a3**2 - 448*a1**3*a2**2*a3 - 960*a1**3*a3*a4 + 112*a1**2*a2**2*a4 + 1536*a1**2*a2*a3**2 + 1600*a1**2*a3 + 224*a1**2*a4**2 + 672*a1*a2**3*a3 + 728*a1*a2**2 - 2788*a1*a2*a3*a4 - 2112*a1*a3**3 + 952*a1*a4 - 77*a2**3*a4 - 1560*a2**2*a3**2 + 1248*a2*a3 + 770*a2*a4**2 + 7392*a3**2*a4 - 15288
r3 = 128*a1**4*a3*a4 - 224*a1**3*a2**2*a4 + 128*a1**3*a3 - 448*a1**3*a4**2 - 224*a1**2*a2**2 + 768*a1**2*a2*a3*a4 + 560*a1**2*a4 + 336*a1*a2**3*a4 + 872*a1*a2*a3 - 1176*a1*a2*a4**2 - 1056*a1*a3**2*a4 + 1008*a1 + 154*a2**3 - 780*a2**2*a3*a4 + 644*a2*a4 - 1056*a3**2 + 3432*a3*a4**2
ok2 = True
for i, r in enumerate([r0, r1, r2, r3]):
    v = sp.expand(r.subs({a1: A1, a2: A2, a3: A3}))
    num, den = sp.together(v).as_numer_denom()
    rem = sp.rem(sp.Poly(num, a4), TP)
    status = "vanishes" if rem.as_expr() == 0 else f"FAILS: {rem.as_expr()}"
    print(f"r{i} {status}")
    if rem.as_expr() != 0: ok2 = False
print(f"\nAll residuals vanish mod T: {ok2}")
print(f"\n=== OVERALL: {'PASS' if (ok and ok2) else 'FAIL'} ===")
