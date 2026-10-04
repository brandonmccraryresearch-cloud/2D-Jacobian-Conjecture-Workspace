# exact arithmetic in K5 = Q[w]/(R) using python-flint fmpq_poly
import flint, json
Rp = flint.fmpq_poly([26, 0, 3, 3, -1, 1])   # 26 + 3w^2 + 3w^3 - w^4 + w^5
class K5:
    __slots__ = ('p',)
    def __init__(self, p):
        if not isinstance(p, flint.fmpq_poly): p = flint.fmpq_poly(p if isinstance(p, list) else [p])
        self.p = p % Rp
    def __add__(s, o): o = o if isinstance(o, K5) else K5(o); return K5(s.p + o.p)
    __radd__ = __add__
    def __sub__(s, o): o = o if isinstance(o, K5) else K5(o); return K5(s.p - o.p)
    def __rsub__(s, o): return K5(o) - s
    def __neg__(s): return K5(-s.p)
    def __mul__(s, o): o = o if isinstance(o, K5) else K5(o); return K5(s.p * o.p)
    __rmul__ = __mul__
    def inv(s):
        g, a, b = s.p.xgcd(Rp)   # a*s + b*R = g
        assert g.degree() == 0
        return K5(a / g[0])
    def __truediv__(s, o): o = o if isinstance(o, K5) else K5(o); return s * o.inv()
    def __pow__(s, e):
        r = K5(1); b = s
        while e:
            if e & 1: r = r * b
            b = b * b; e >>= 1
        return r
    def is_zero(s): return s.p.degree() < 0
    def coeffs(s): return [s.p[i] for i in range(5)]
    def __repr__(s): return str(s.p)
import os
HERE = os.path.dirname(os.path.abspath(__file__))
def _q(c): return flint.fmpq(*map(int, c.split('/'))) if '/' in c else flint.fmpq(int(c))
def lean_point():
    """The K5 chart point of `ChartClassification` (certgen/chartpoint.json: P[j] = a_j, Q[k] = b_k)."""
    d = json.load(open(os.path.join(HERE, '..', 'chartpoint.json')))
    pt = {f'a{j}': K5(flint.fmpq_poly([_q(c) for c in d['P'][str(j)]])) for j in range(1, 8)}
    pt.update({f'b{k}': K5(flint.fmpq_poly([_q(c) for c in d['Q'][str(k)]])) for k in range(10)})
    return pt
