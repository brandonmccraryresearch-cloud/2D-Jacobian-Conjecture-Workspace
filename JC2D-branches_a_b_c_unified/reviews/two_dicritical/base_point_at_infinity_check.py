"""Every Keller map of degree >= 2 has a base point at infinity (review of 2026-10-12, section 9.3, as corrected).

Claim. Let F = (P, Q) have [P, Q] = c != 0 and d = max(deg P, deg Q) >= 2. Homogenize the pencil lambda P + mu Q at
degree d. Then P^h and Q^h have a common zero on the line at infinity L = {Z = 0} (over the algebraic closure).
  - deg P = deg Q = d: the degree-(2d-2) part of [P, Q] is [P_d, Q_d], and 2d - 2 >= 2, so [P_d, Q_d] = 0. For
    nonzero binary forms f, g of the same degree e >= 1, [f, g] = 0 forces f = r g with r constant: h = f/g has
    degree 0, so x h_x + y h_y = 0 (Euler), and [h, g] = [f, g]/g = 0; if (h_x, h_y) != 0 both relations make
    (g_x, g_y) proportional to (-y, x), so x g_x + y g_y = e g = 0, a contradiction. So P_d = r Q_d, and every zero
    of Q_d on L is a common zero.
  - deg P = d > deg Q: Q^h = Z^(d - deg Q) (...) vanishes on all of L, and P_d has a zero on L.
With a translation of the target that makes 0 a value of F (no translation is needed for an automorphism), the pencil
also has an affine base point. Since every base point carries a dicritical (section 9.3), the statement as worded
fails for every Keller map of degree >= 2. Affine maps are the exception: the identity has no base point at infinity.

Checks (each prints PASS or FAIL; exit 1 on any FAIL):
  1. for random binary forms f of degree e = 1..6, the forms g of degree e with [f, g] = 0 are exactly span{f};
  2. 30 random automorphisms (compositions of triangular and linear maps) of degree >= 2: [P, Q] is a nonzero
     constant, and the top forms (or P_d alone, for unequal degrees) have a common zero on L: the gcd has degree >= 1;
  3. control: affine maps of determinant != 0 have no base point at infinity (the gcd of the linear top forms is 1).
"""
import random
import sys

import sympy as sp

x, y, X, Y = sp.symbols('x y X Y')
FAILS = []


def check(name, ok, detail=''):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f": {detail}" if detail else ''))
    if not ok:
        FAILS.append(name)


def jac(P, Q):
    return sp.expand(sp.diff(P, x) * sp.diff(Q, y) - sp.diff(P, y) * sp.diff(Q, x))


def top_form(S):
    p = sp.Poly(S, x, y)
    d = p.total_degree()
    return d, sp.expand(sum(c * x ** i * y ** j for (i, j), c in p.terms() if i + j == d))


random.seed(9313)
print('1. Binary forms with vanishing Jacobian are proportional')
ok = True
for e in range(1, 7):
    for trial in range(3):
        f = sum(random.randint(-4, 4) * x ** i * y ** (e - i) for i in range(e + 1))
        if f == 0:
            continue
        cs = sp.symbols(f'g0:{e + 1}')
        g = sum(cs[i] * x ** i * y ** (e - i) for i in range(e + 1))
        J = sp.Poly(jac(f, g), x, y)
        A = sp.Matrix([[sp.diff(cf, c) for c in cs] for cf in J.coeffs()])
        ns = A.nullspace()
        fco = [sp.Poly(f, x, y).coeff_monomial(x ** i * y ** (e - i)) for i in range(e + 1)]
        ok &= len(ns) == 1 and sp.Matrix([fco, list(ns[0])]).rank() == 1
check('for 18 random forms f of degree 1..6, {g : [f, g] = 0} = span{f}', ok)


def rand_poly1(var, deg):
    return sum(random.randint(-3, 3) * var ** k for k in range(2, deg + 1)) + random.choice([-2, -1, 1, 2]) * var ** deg


print('2. Random automorphisms of degree >= 2')
count = 0
ok_all = True
while count < 30:
    P, Q = x, y
    for step in range(random.randint(2, 3)):
        kind = random.choice(['tx', 'ty', 'lin'])
        if kind == 'tx':
            P, Q = sp.expand(P + rand_poly1(Q, random.randint(2, 3))), Q
        elif kind == 'ty':
            P, Q = P, sp.expand(Q + rand_poly1(P, random.randint(2, 3)))
        else:
            m = sp.Matrix([[random.randint(-2, 2) for _ in range(2)] for _ in range(2)])
            if m.det() == 0:
                continue
            P, Q = sp.expand(m[0, 0] * P + m[0, 1] * Q), sp.expand(m[1, 0] * P + m[1, 1] * Q)
    dP, tP = top_form(P)
    dQ, tQ = top_form(Q)
    if max(dP, dQ) < 2 or max(dP, dQ) > 12:
        continue
    c = jac(P, Q)
    keller = c.is_number and c != 0
    if dP == dQ:
        g = sp.gcd(sp.Poly(tP, x, y), sp.Poly(tQ, x, y))
    elif dP > dQ:
        g = sp.Poly(tP, x, y)
    else:
        g = sp.Poly(tQ, x, y)
    ok = keller and g.total_degree() >= 1 and (dP != dQ or sp.Poly(jac(tP, tQ), x, y).is_zero)
    ok_all &= ok
    count += 1
    print(f'  degrees ({dP}, {dQ}), [P,Q] = {c}, common factor of the top forms on L of degree {g.total_degree()}'
          + ('' if ok else '  <-- FAIL'))
check('30 random automorphisms of degree >= 2: Keller, and a base point at infinity', ok_all)

print('3. Control: affine maps')
ok = True
for trial in range(10):
    m = sp.Matrix([[random.randint(-3, 3) for _ in range(2)] for _ in range(2)])
    if m.det() == 0:
        continue
    P = m[0, 0] * x + m[0, 1] * y + random.randint(-3, 3)
    Q = m[1, 0] * x + m[1, 1] * y + random.randint(-3, 3)
    _, tP = top_form(P)
    _, tQ = top_form(Q)
    ok &= sp.gcd(sp.Poly(tP, x, y), sp.Poly(tQ, x, y)).total_degree() == 0
check('affine maps with nonzero determinant: no base point at infinity', ok)

print('RESULT:', 'PASS' if not FAILS else f'FAIL {FAILS}')
sys.exit(1 if FAILS else 0)
