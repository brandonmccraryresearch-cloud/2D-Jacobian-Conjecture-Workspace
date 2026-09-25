"""
weights.py -- split the generated system by the grading w(x^i y^j) = j - 2i.
Prints, for every bracket monomial weight, which coefficient-variables occur.
This checks (not assumes) the claimed triangular structure.
"""
from gen_system import build

LP, LQ, eqs, tgt = build()
w = lambda ij: ij[1] - 2 * ij[0]
print("P weights:", sorted({w(p) for p in LP}), " Q weights:", sorted({w(q) for q in LQ}))
byw = {}
for key, terms in eqs.items():
    byw.setdefault(w(key), []).append((key, terms))
for W in sorted(byw, reverse=True):
    pw = sorted({w(tuple(map(int, p.split('_')[1:]))) for key, T in byw[W] for c, p, q in T})
    qw = sorted({w(tuple(map(int, q.split('_')[1:]))) for key, T in byw[W] for c, p, q in T})
    print(f"bracket weight {W:3d}: #eqs={len(byw[W]):3d}  P-weights used {pw}  Q-weights used {qw}")
print("target monomial", tgt, "has weight", w(tgt))
