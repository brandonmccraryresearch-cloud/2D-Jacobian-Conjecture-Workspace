# Weighted-homogeneous certificate search: y7^m * g = sum_k C_k * S_k  (k = 11..16), exact over Q.
import flint, sympy as sp, itertools, sys, time, pickle
from yform import S_list, Y
from interp import monos, relations
S = S_list(16)
def to_dict(p):
    P = sp.Poly(sp.expand(p), *Y); return {m: flint.fmpq(int(sp.Rational(c).p), int(sp.Rational(c).q)) for m, c in P.terms()}
SD = {k: to_dict(S[k]) for k in range(11, 17)}
def addm(a, b): return tuple(x + y for x, y in zip(a, b))
def solve_affine(eqrows, rhs, nunk):
    """Solve M x = rhs (sparse rows as dicts col->val). Return particular solution (free vars 0) or None."""
    rows = [[r.get(c, flint.fmpq(0)) for c in range(nunk)] + [rhs[i]] for i, r in enumerate(eqrows)]
    A = flint.fmpq_mat(len(rows), nunk + 1, [x for r in rows for x in r])
    R, rank = A.rref()
    x = [flint.fmpq(0)] * nunk; r = 0; piv = []
    for c in range(nunk + 1):
        if r < rank and R[r, c] != 0:
            if c == nunk: return None   # inconsistent
            piv.append((r, c)); r += 1
    for (r, c) in piv: x[c] = R[r, nunk]
    return x
def certificate(g, m):
    """g: dict mono->fmpq, weighted homogeneous. Returns dict k -> (dict mono->coef) or None."""
    wg = sum((i + 1) * e for m_ in g for i, e in enumerate(m_)) // len(g) if g else 0
    wg = sum((i + 1) * e for i, e in enumerate(next(iter(g))))
    W = wg + 7 * m
    unk = []   # (k, mono)
    for k in range(11, 17):
        if W - k >= 0:
            for mm in monos(W - k): unk.append((k, mm))
    col = {u: i for i, u in enumerate(unk)}
    target = {}
    for mm, c in g.items(): target[addm(mm, (0,)*6 + (m,))] = c
    eqmon = monos(W); eqi = {mm: i for i, mm in enumerate(eqmon)}
    rows = [dict() for _ in eqmon]
    for (k, mm), ci in col.items():
        for sm, sc in SD[k].items():
            t = addm(mm, sm); rows[eqi[t]][ci] = rows[eqi[t]].get(ci, flint.fmpq(0)) + sc
    rhs = [target.get(mm, flint.fmpq(0)) for mm in eqmon]
    x = solve_affine(rows, rhs, len(unk))
    if x is None: return None, len(unk), len(eqmon)
    C = {}
    for (k, mm), ci in col.items():
        if x[ci] != 0: C.setdefault(k, {})[mm] = x[ci]
    return C, len(unk), len(eqmon)
if __name__ == '__main__':
    gens = {}
    for w in (4, 5, 6, 7):
        ms, rels = relations(w)
        gens[w] = rels
    # pick a basis for new generators: all relations at each weight (redundant ones will also get certificates; fine for probing)
    for w in (4, 5, 6, 7):
        for j, g in enumerate(gens[w]):
            for m in range(0, 4):
                t = time.time(); C, nu, ne = certificate(g, m)
                if C is not None:
                    nt = sum(len(v) for v in C.values())
                    mx = max(max(len(str(c.p)), len(str(c.q))) for v in C.values() for c in v.values())
                    print(f"w={w} rel#{j} ({len(g)} terms): y7^{m} OK  unknowns={nu} eqs={ne} cert_terms={nt} maxdigits={mx} ({time.time()-t:.1f}s)")
                    break
                else:
                    print(f"w={w} rel#{j}: y7^{m} infeasible (unknowns={nu}, eqs={ne}) ({time.time()-t:.1f}s)")
