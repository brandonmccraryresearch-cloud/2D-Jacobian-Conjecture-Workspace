import sympy as sp

# Variables
a1, a2, a3, a4 = sp.symbols('a1 a2 a3 a4')

# 10 GB elements from Singular
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
    a1*a3*a4 - 49*a4**2 + 117*a3
]

T = 9*a4**10 + 37200*a4**5 + 95051008

print("Total GB polynomials:", len(gb))

# Notice eq 5: 21*a4^3 - 72*a3*a4 + 91*a2 = 0
# Notice eq 6: 12*a3*a4^2 - 99*a2*a4 + 416*a1 = 0
# Notice eq 7: a2*a4^2 - 10*a1*a4 + 182 = 0
# Can we solve for a1, a2, a3 as rational functions of a4?
# From eq 5: 91*a2 = 72*a3*a4 - 21*a4^3  => a2 = (72*a3*a4 - 21*a4^3)/91
# Let's check linear equations in a1, a2, a3!
# Over Q(a4), let's see the linear relations among a1, a2, a3:
# eq 5: 91*a2 - 72*a4*a3 = -21*a4^3
# eq 6: 416*a1 - 99*a4*a2 + 12*a4^2*a3 = 0
# eq 7: -10*a4*a1 + a4^2*a2 = -182

M = sp.Matrix([
    [0, 91, -72*a4],
    [416, -99*a4, 12*a4**2],
    [-10*a4, a4**2, 0]
])
rhs = sp.Matrix([
    -21*a4**3,
    0,
    -182
])

print("Det of M:", sp.factor(M.det()))

# Solve linear system M * [a1, a2, a3]^T = rhs
sol = M.LUsolve(rhs)
a1_expr = sp.factor(sol[0])
a2_expr = sp.factor(sol[1])
a3_expr = sp.factor(sol[2])

print("a1 =", a1_expr)
print("a2 =", a2_expr)
print("a3 =", a3_expr)

# Reduce modulo T:
# In Q[a4]/(T), simplify each expression
def mod_T(expr):
    num, den = sp.together(expr).as_numer_denom()
    # invert den mod T
    s, t, g = sp.gcdex(sp.Poly(den, a4), sp.Poly(T, a4))
    assert g.total_degree() == 0, f"gcd with T is {g}"
    inv_den = s / g.as_expr()
    rem = sp.rem(sp.Poly(num * inv_den, a4), sp.Poly(T, a4))
    return rem.as_expr()

a1_mod = mod_T(a1_expr)
a2_mod = mod_T(a2_expr)
a3_mod = mod_T(a3_expr)

print("\n--- Canonical polynomial representatives in Q[a4]/(T) ---")
print("a1 =", sp.Poly(a1_mod, a4))
print("a2 =", sp.Poly(a2_mod, a4))
print("a3 =", sp.Poly(a3_mod, a4))

# Now verify that substituting (a1_mod, a2_mod, a3_mod, a4) into all 10 GB relations yields 0 mod T
all_zero = True
for idx, poly in enumerate(gb):
    val = poly.subs({a1: a1_mod, a2: a2_mod, a3: a3_mod})
    rem = sp.rem(sp.Poly(sp.expand(val), a4), sp.Poly(T, a4))
    if rem.as_expr() != 0:
        print(f"GB[{idx}] non-zero remainder: {rem}")
        all_zero = False

print("\nAll 10 GB elements vanish modulo T:", all_zero)

# Also check original 4 residuals:
import sys
sys.path.append('/home/ubuntu/gghv')
from generate_m5_singular_q import *
A = [1, a1_mod, a2_mod, a3_mod, a4, 1]
e = 7
B = [1] + [None]*e
for n in range(1, e+1):
    known = sum((1 + 2*(n-i) - 3*i)*A[i]*B[n-i] for i in range(1, 6) if 0 <= n-i <= e)
    B[n] = sp.cancel(-known/(1 + 2*n))

all_res_zero = True
for n in range(8, 13):
    s = sum((1 + 2*(n-i) - 3*i)*A[i]*B[n-i] for i in range(6) if 0 <= n-i <= e)
    num, _ = sp.together(s).as_numer_denom()
    rem = sp.rem(sp.Poly(num, a4), sp.Poly(T, a4))
    if rem.as_expr() != 0:
        print(f"Residual n={n} non-zero remainder: {rem}")
        all_res_zero = False
    else:
        print(f"Residual n={n} vanishes exactly mod T")

print("All original residuals vanish modulo T:", all_res_zero)
