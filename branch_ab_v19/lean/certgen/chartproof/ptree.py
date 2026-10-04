# A polynomial "tree" shared by the Lean reflected Expr printer and the Lean text printer, so that
# `Expr.denote ctx e` is definitionally the printed text (same shape, same numerals).
import sympy as sp
def poly_tree(P, gens):
    """P with integer coefficients. Returns tree: ('add', l, r) | ('term', c, [(i, e), ...])."""
    Pp = sp.Poly(sp.expand(P), *gens)
    terms = []
    for mon, c in Pp.terms():
        c = int(c); assert c != 0
        terms.append(('term', c, [(i, e) for i, e in enumerate(mon) if e > 0]))
    if not terms: return ('term', 0, [])
    def bal(lst):
        if len(lst) == 1: return lst[0]
        mid = len(lst) // 2
        return ('add', bal(lst[:mid]), bal(lst[mid:]))
    return bal(terms)
def _mon_expr(mon):
    fs = [f"(.var {i})" if e == 1 else f"(.pow (.var {i}) {e})" for i, e in mon]
    t = fs[0]
    for f in fs[1:]: t = f"(.mul {t} {f})"
    return t
def _mon_text(mon, names):
    return ' * '.join(names[i] if e == 1 else f"{names[i]} ^ {e}" for i, e in mon)
def tree_expr(T):
    if T[0] == 'add': return f"(.add {tree_expr(T[1])} {tree_expr(T[2])})"
    _, c, mon = T
    if not mon: return f"(.num {c})" if c >= 0 else f"(.num ({c}))"
    m = _mon_expr(mon)
    if c == 1: return m
    if c == -1: return f"(.neg {m})"
    return f"(.mul (.num {c}) {m})" if c > 0 else f"(.mul (.num ({c})) {m})"
def tree_text(T, names):
    if T[0] == 'add': return f"({tree_text(T[1], names)} + {tree_text(T[2], names)})"
    _, c, mon = T
    if not mon: return f"({c} : L)"
    m = _mon_text(mon, names)
    if c == 1: return f"({m})"
    if c == -1: return f"(-({m}))"
    return f"(({c} : L) * ({m}))"
