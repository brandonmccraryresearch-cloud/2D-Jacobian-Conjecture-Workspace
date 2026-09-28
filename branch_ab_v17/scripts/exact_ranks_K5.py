# Attribution: computed by the referee (Claude/Anthropic, Tier 1 agent) during Round 6 review.
# Part of the characteristic-0 verification for the branch-(a,b) elimination.

"""
exact_ranks_K5.py -- EXACT characteristic-0 ranks of the paper's descent operators, over
K5 = Q[w]/(w^5 - w^4 + 3w^3 + 3w^2 + 26), at the exactly verified top-layer point
(e5_exact_K5.json, normalisation a_1_0 = b_2_1 = a_2_2 = 1).
Ranks are invariant under the torus/mu_7 rescaling (invertible row/column scalings) and under
Galois conjugation, so one computation covers all 35 top-layer points.
Operators (built from my own generic equation generator, not from the paper's code):
  E4 : Jacobian of the weight -3 block w.r.t. (A1, B2) = (a_{i,2i-1}, b_{k,2k-2})   [18 x 19]
  E3 : Jacobian of the weight -2 block w.r.t. (A0, B1) = (a_{i,2i},   b_{k,2k-1})   [19 x 20]
  E2 : Jacobian of the weight -1 block w.r.t. B0       = (b_{k,2k}, k>=1)           [19 x 12]
Paper's claims (mod 101): rank E4 = 17, rank E3 = 18, rank E2 = 12.
Also computes, over K5, whether E3 is solvable for every t (left null vector kills K_ij).
"""
import json, sys
from flint import fmpq_poly, fmpq
sys.path.insert(0, ".")
from gen_system import build

Rr = fmpq_poly([26, 0, 3, 3, -1, 1])
def K(coeffs):
    return fmpq_poly([fmpq(*map(int, c.split('/'))) if '/' in c else fmpq(int(c)) for c in coeffs]) % Rr
def inv(a):
    g, s, _ = a.xgcd(Rr)
    assert g == 1
    return s % Rr

d = json.load(open("e5_exact_K5.json"))
pt = {v: K(c) for v, c in d.items() if not v.startswith("_")}
one = fmpq_poly([1])
pt.update({"a_1_0": one, "b_2_1": one, "a_2_2": one})

LP, LQ, eqs, tgt = build()
w = lambda ij: ij[1] - 2 * ij[0]
vw = lambda v: w(tuple(map(int, v.split('_')[1:])))
def rowspace_rank(rows):
    """exact Gaussian elimination over K5; rows = list of lists of fmpq_poly"""
    M = [r[:] for r in rows]
    rank, col = 0, 0
    ncol = len(M[0]) if M else 0
    for col in range(ncol):
        piv = next((i for i in range(rank, len(M)) if M[i][col] != 0), None)
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        iv = inv(M[rank][col])
        M[rank] = [(x * iv) % Rr for x in M[rank]]
        for i in range(len(M)):
            if i != rank and M[i][col] != 0:
                f = M[i][col]
                M[i] = [(M[i][j] - f * M[rank][j]) % Rr for j in range(ncol)]
        rank += 1
    return rank, M

def jacobian(weight, unknowns):
    rows = []
    for k in sorted(eqs):
        if w(k) != weight:
            continue
        row = [fmpq_poly([0])] * len(unknowns)
        idx = {u: i for i, u in enumerate(unknowns)}
        for c, pv, qv in eqs[k]:
            for a, b in ((pv, qv), (qv, pv)):
                if a in idx and b in pt:          # linear in unknown a, coefficient from top layer
                    row[idx[a]] = (row[idx[a]] + c * pt[b]) % Rr
        rows.append(row)
    return rows

key = lambda v: (v[0], int(v.split('_')[1]), int(v.split('_')[2]))
allv = sorted({v for T in eqs.values() for c, pv, qv in T for v in (pv, qv)}, key=key)
A1B2 = [v for v in allv if (v[0] == 'a' and vw(v) == -1) or (v[0] == 'b' and vw(v) == -2)]
A0B1 = [v for v in allv if (v[0] == 'a' and vw(v) == 0 and v != 'a_0_0') or (v[0] == 'b' and vw(v) == -1)]
B0 = [v for v in allv if v[0] == 'b' and vw(v) == 0 and v != 'b_0_0']
print("unknown counts: E4", len(A1B2), " E3", len(A0B1), " E2", len(B0))
for name, W_, U in [("E4", -3, A1B2), ("E3", -2, A0B1), ("E2", -1, B0)]:
    rows = jacobian(W_, U)
    r, _ = rowspace_rank(rows)
    print(f"{name}: {len(rows)} x {len(U)} over K5 (char 0, exact): rank {r}")
