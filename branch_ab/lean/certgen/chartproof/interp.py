# Find all weighted-homogeneous relations of weight w vanishing on the Lean-slice orbit point (exact, over Q)
import flint, itertools, sys
from linalg import nullspace_q
from k5 import K5, lean_point
P = lean_point()
a7 = P['a7']; y7 = a7.inv()
Yv = [P[f'a{7-i}'] * y7 for i in range(1, 7)] + [y7]     # y1..y7 at the Lean-slice point
def monos(w, maxv=7):
    # exponent vectors e (len 7) with sum (i+1)*e_i = w
    res = []
    def rec(i, rem, cur):
        if i < 0:
            if rem == 0: res.append(tuple(cur))
            return
        wt = i + 1
        for e in range(rem // wt + 1):
            cur[i] = e; rec(i - 1, rem - e * wt, cur)
        cur[i] = 0
    rec(maxv - 1, w, [0]*maxv); return res
pw = [[K5(1)] for _ in range(7)]
def ypow(i, e):
    while len(pw[i]) <= e: pw[i].append(pw[i][-1] * Yv[i])
    return pw[i][e]
def mval(m):
    r = K5(1)
    for i, e in enumerate(m):
        if e: r = r * ypow(i, e)
    return r
def relations(w):
    ms = monos(w); vals = [mval(m).coeffs() for m in ms]
    rows = [[vals[j][i] for j in range(len(ms))] for i in range(5)]
    rels = []
    for vec in nullspace_q(rows, len(ms)):
        rels.append({ms[r]: vec[r] for r in range(len(ms)) if vec[r] != 0})
    return ms, rels
if __name__ == '__main__':
    for w in range(1, 9):
        ms, rels = relations(w)
        print(f"weight {w}: {len(ms)} monomials, {len(rels)} independent relations")
