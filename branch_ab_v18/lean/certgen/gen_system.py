"""
gen_system.py -- build the polynomial system  [P,Q] = lam * x^2  directly from the
Newton polygons in the brief, with no hand-derived reformulation in between.

Unknowns : a_i_j  for (i,j) in N(P) cap Z^2,   b_i_j for (i,j) in N(Q) cap Z^2,  lam.
Bracket  : [P,Q] = P_x Q_y - P_y Q_x   (GGHV p.1 convention, same as the brief).
Coefficient of x^A y^B in [P,Q]:
     sum_{(i,j) in N(P), (k,l) in N(Q), i+k-1=A, j+l-1=B}  (i*l - j*k) a_ij b_kl .
Output: list of equations  coeff(x^A y^B) - lam*[A==2 and B==0]  (all must vanish).
"""
from fractions import Fraction
from itertools import product


def hull(pts):
    """Andrew monotone chain, returns CCW vertex list (no collinear points)."""
    pts = sorted(set(pts))
    if len(pts) <= 2:
        return pts

    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
    lo, up = [], []
    for p in pts:
        while len(lo) >= 2 and cross(lo[-2], lo[-1], p) <= 0:
            lo.pop()
        lo.append(p)
    for p in reversed(pts):
        while len(up) >= 2 and cross(up[-2], up[-1], p) <= 0:
            up.pop()
        up.append(p)
    return lo[:-1] + up[:-1]


def lattice_points(verts):
    """All integer points in conv(verts) (closed), via half-planes of the CCW hull."""
    H = hull(verts)
    assert sorted(H) == sorted(set(verts)), ("some listed point is not a vertex", H, verts)
    xs = [v[0] for v in verts]; ys = [v[1] for v in verts]
    out = []
    n = len(H)
    for i in range(min(xs), max(xs) + 1):
        for j in range(min(ys), max(ys) + 1):
            ok = True
            for e in range(n):
                (x0, y0), (x1, y1) = H[e], H[(e + 1) % n]
                if (x1 - x0) * (j - y0) - (y1 - y0) * (i - x0) < 0:
                    ok = False
                    break
            if ok:
                out.append((i, j))
    return sorted(out)


NP_VERTS = [(0, 0), (1, 0), (8, 14), (8, 16)]
NQ_VERTS = [(0, 0), (2, 1), (12, 21), (12, 24)]
TARGET = (2, 0)          # lam * x^2


def build(np_verts=NP_VERTS, nq_verts=NQ_VERTS, target=TARGET):
    LP = lattice_points(np_verts)
    LQ = lattice_points(nq_verts)
    eqs = {}     # (A,B) -> list of (coef, pvar, qvar)
    for (i, j), (k, l) in product(LP, LQ):
        c = i * l - j * k
        if c == 0:
            continue
        key = (i + k - 1, j + l - 1)
        eqs.setdefault(key, []).append((c, f"a_{i}_{j}", f"b_{k}_{l}"))
    if target not in eqs:
        eqs[target] = []
    return LP, LQ, eqs, target


def to_strings(eqs, target, lamname="lam"):
    out = []
    for key in sorted(eqs):
        terms = [f"({c})*{p}*{q}" for c, p, q in eqs[key]]
        s = "+".join(terms) if terms else "0"
        if key == target:
            s += f"-{lamname}"
        out.append((key, s))
    return out


if __name__ == "__main__":
    LP, LQ, eqs, tgt = build()
    print("#lattice points N(P):", len(LP))
    print("#lattice points N(Q):", len(LQ))
    print("#nonzero bracket monomials (equations):", len(eqs))
    print("N(P) points:", LP)
    print("N(Q) points:", LQ)
