"""Theorem thm:main of two_dicritical_closure.tex, read literally, against polynomial automorphisms.

thm:main: "Let K be a field of characteristic 0. Let P, Q in K[x,y] with [P,Q] = c in K^x. Then the resolution of the
pencil lambda*P + mu*Q contains no two distinct dicritical divisors."

Criterion used: a divisor E over P^2 (reached by point blowups) is dicritical for the pencil iff the residue of the
rational function Phi = P/Q on E is non-constant. Such an E appears in every resolution of the pencil: if the center of
its valuation on a resolution X were a point q, Phi would be regular at q (X resolves the pencil) and its residue
would be the constant Phi(q). Every base point of a pencil carries at least one dicritical (standard: the exceptional
curve over a base point is connected; if all of it lay in one fiber Phi = t0, a member with t != t0, which passes
through the base point, would meet it).

For each map: the Jacobian; the base points of the pencil homogenized to degree max(deg P, deg Q); and, over each base
point, an explicit chain of blowups ending at a divisor on which Phi has non-constant residue.
Control: the identity (x, y), which must give exactly one base point.
"""
import sympy as sp

x, y, X, Y, Z, t, u = sp.symbols('x y X Y Z t u')


def jac(P, Q):
    return sp.expand(sp.diff(P, x) * sp.diff(Q, y) - sp.diff(P, y) * sp.diff(Q, x))


def homog(F, d):
    return sp.expand(Z ** d * F.subs({x: X / Z, y: Y / Z}, simultaneous=True))


def base_points(Ph, Qh):
    pts = set()
    for (chart, vars_) in [({Z: 1}, (X, Y)), ({Y: 1}, (X, Z)), ({X: 1}, (Y, Z))]:
        for sol in sp.solve([Ph.subs(chart), Qh.subs(chart)], vars_, dict=True):
            pt = {X: chart.get(X, sol.get(X)), Y: chart.get(Y, sol.get(Y)), Z: chart.get(Z, sol.get(Z))}
            if any(v is None for v in pt.values()):
                raise ValueError(f'positive-dimensional base locus in chart {chart}: {sol}')
            # normalize: divide by the last nonzero coordinate
            coords = [pt[X], pt[Y], pt[Z]]
            k = max(i for i, c in enumerate(coords) if c != 0)
            pts.add(tuple(sp.nsimplify(c / coords[k]) for c in coords))
    return sorted(pts, key=str)


def residue(Phi, var):
    """Phi restricted to the exceptional divisor {var = 0}: from the reduced fraction N/D, N(0)/D(0) when D(0) != 0,
    the constant oo when D(0) = 0 != N(0). (Both zero would mean a common factor of var, impossible after cancel.)"""
    num, den = sp.fraction(sp.cancel(sp.together(Phi)))
    n0, d0 = sp.expand(num.subs(var, 0)), sp.expand(den.subs(var, 0))
    if d0 == 0:
        assert n0 != 0
        return sp.oo
    return sp.simplify(n0 / d0)


def report(name, P, Q, chains):
    d = max(sp.Poly(P, x, y).total_degree(), sp.Poly(Q, x, y).total_degree())
    Ph, Qh = homog(P, d), homog(Q, d)
    print(f'== {name}: P = {P}, Q = {Q}; [P,Q] = {jac(P, Q)}; pencil homogenized to degree {d}: '
          f'{Ph}, {Qh}')
    print(f'   base points [X:Y:Z]: {base_points(Ph, Qh)}')
    for label, Phi, var, other in chains:
        r = residue(Phi, var)
        nonconst = r != sp.oo and sp.diff(r, other) != 0
        print(f'   {label}: residue of Phi on the last divisor = {r}; non-constant (dicritical): {nonconst}')


# Identity (control): one base point (the origin); blowup x = x, y = x*t: Phi = x/(x t) = 1/t.
report('identity (control)', x, y,
       [('over [0:0:1], one blowup (y = x t)', (x) / (x * t), x, t)])

# (x - y^2, y): base points [0:0:1] and [1:0:0].
#  over the origin: y = x t: Phi = (x - x^2 t^2)/(x t)
#  over [1:0:0], chart X = 1, coordinates (Y, Z) = (y_, z_): Phi = (Z - Y^2)/(Y Z);
#   blowups: Z = Y z1; z1 = Y z2; z2 = 1 + Y z3  (each at the base point of the previous divisor)
y_, z1, z2, z3 = sp.symbols('y_ z1 z2 z3')
Phi_inf = (Z - Y ** 2) / (Y * Z)
s1 = Phi_inf.subs({Z: y_ * z1, Y: y_})
s2 = s1.subs(z1, y_ * z2)
s3 = s2.subs(z2, 1 + y_ * z3)
report('automorphism (x - y^2, y)', x - y ** 2, y,
       [('over [0:0:1], one blowup (y = x t)', (x - x ** 2 * t ** 2) / (x * t), x, t),
        ('over [1:0:0], first blowup (Z = Y z1)', s1, y_, z1),
        ('over [1:0:0], second blowup (z1 = Y z2)', s2, y_, z2),
        ('over [1:0:0], third blowup (z2 = 1 + Y z3)', s3, y_, z3)])

# (x, y + x^2): base points [0:0:1] and [0:1:0].
#  over [0:1:0], chart Y = 1, coordinates (X, Z): Phi = X Z/(Z + X^2) (P^h = X Z, Q^h = Y Z + X^2 at Y = 1)
x_, w1, w2, w3 = sp.symbols('x_ w1 w2 w3')
Psi_inf = (X * Z) / (Z + X ** 2)
r1 = Psi_inf.subs({Z: x_ * w1, X: x_})
r2 = r1.subs(w1, x_ * w2)
r3 = r2.subs(w2, -1 + x_ * w3)
report('automorphism (x, y + x^2)', x, y + x ** 2,
       [('over [0:0:1], one blowup (y = x t)', x / (x * t + x ** 2), x, t),
        ('over [0:1:0], first blowup (Z = X w1)', r1, x_, w1),
        ('over [0:1:0], second blowup (w1 = X w2)', r2, x_, w2),
        ('over [0:1:0], third blowup (w2 = -1 + X w3)', r3, x_, w3)])
