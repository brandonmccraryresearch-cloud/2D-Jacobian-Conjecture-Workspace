# Common helpers: symbols, Lean printing, exact identity checking.
import sympy as sp, flint
A = sp.symbols('a1:8'); B = sp.symbols('b0:10'); Y = sp.symbols('y1:8')
w, z, t, s, y7s = sp.symbols('w z t s y7')
def Q(c):
    """sympy Rational from fmpq/int/str"""
    if isinstance(c, flint.fmpq): return sp.Rational(int(c.p), int(c.q))
    return sp.Rational(c)
def lean_num(c):
    c = sp.Rational(c)
    if c.q == 1: return f"({c.p} : L)"
    return f"(({c.p} : L) / {c.q})"
def lean_poly(expr, gens):
    """Print a polynomial (sympy expr) as a Lean term over L."""
    P = sp.Poly(sp.expand(expr), *gens)
    if P.is_zero: return "(0 : L)"
    parts = []
    for mon, c in P.terms():
        m = ' * '.join((f"{g} ^ {e}" if e > 1 else f"{g}") for g, e in zip(gens, mon) if e > 0)
        cs = lean_num(c)
        parts.append(cs + (' * ' + m if m else ''))
    return ' + '.join(parts)
def check_lc(goal_lhs, goal_rhs, terms):
    """Verify goal_lhs - goal_rhs - sum(coef*(h_lhs - h_rhs)) == 0 exactly. terms: list of (coef, h_lhs, h_rhs)."""
    e = sp.expand(goal_lhs - goal_rhs - sum(c * (hl - hr) for c, hl, hr in terms))
    return e == 0
def lc_text(terms_named, gens):
    """terms_named: list of (coef_expr, hypname). Returns linear_combination argument text."""
    out = []
    for c, h in terms_named:
        c = sp.expand(c)
        if c == 0: continue
        out.append(f"({lean_poly(c, gens)}) * {h}")
    return ' + '.join(out) if out else '0'
