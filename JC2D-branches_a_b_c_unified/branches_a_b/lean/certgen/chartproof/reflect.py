# Emit Lean.Grind.CommRing.Expr terms for integer polynomials.
import sympy as sp
def expr_of_poly(P, gens, name_prefix='E'):
    """P: sympy polynomial with integer coefficients. Returns Lean Expr term (balanced sum)."""
    Pp = sp.Poly(sp.expand(P), *gens)
    terms = []
    for mon, c in Pp.terms():
        c = int(c)
        facs = []
        for i, e in enumerate(mon):
            if e == 1: facs.append(f"(.var {i})")
            elif e > 1: facs.append(f"(.pow (.var {i}) {e})")
        t = f"(.num {c})" if c >= 0 else f"(.num ({c}))"
        for f in facs: t = f"(.mul {t} {f})"
        terms.append(t)
    if not terms: return "(.num 0)"
    def bal(lst):
        if len(lst) == 1: return lst[0]
        mid = len(lst) // 2
        return f"(.add {bal(lst[:mid])} {bal(lst[mid:])})"
    return bal(terms)
def rarray(names):
    """balanced RArray over the given Lean variable names (indices 0..n-1)."""
    def build(lo, hi):   # [lo, hi)
        if hi - lo == 1: return f"(.leaf {names[lo]})"
        mid = (lo + hi) // 2
        return f"(.branch {mid} {build(lo, mid)} {build(mid, hi)})"
    return build(0, len(names))
def int_scale(P, gens):
    Pp = sp.Poly(sp.expand(P), *gens); d = 1
    for c in Pp.coeffs(): d = sp.ilcm(d, sp.Rational(c).q)
    return d
