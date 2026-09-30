"""ops_c.py -- the branch-(c) layer operators E2 ... E_{-2} over K5, read off the full bracket
equations of each weight (certgen/gen_system.build with the branch-(c) polygons): the operator is the
part of each weight-block that is linear in the new layer unknowns (paired with the top layer); rows
of the block with no unknown are pure conditions.  Top layer: the rescaled K5 point of cert.json
(torus-equivalent to the pipeline's a_{2,2} = 1 normalisation; ranks are torus-invariant)."""
import json, os, sys
from flint import fmpq_poly, fmpq
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "certgen"))
from gen_system import build
Rr = fmpq_poly([26, 0, 3, 3, -1, 1]); ZERO = fmpq_poly([0]); ONE = fmpq_poly([1])
def Kc(c): return fmpq_poly([fmpq(*map(int, s.split('/'))) if '/' in s else fmpq(int(s)) for s in c]) % Rr
def inv(a):
    g, s, _ = a.xgcd(Rr); assert g == 1; return s % Rr
cert = json.load(open(os.path.join(HERE, "..", "certgen", "cert.json")))
top = {v: Kc(c) for v, c in cert["top"].items()}
NPc = [(0, 0), (1, 0), (8, 14), (8, 16), (0, 8)]; NQc = [(0, 0), (2, 1), (12, 21), (12, 24), (0, 12)]
LPc, LQc, eqsc, _ = build(NPc, NQc)
wt = lambda ij: ij[1] - 2 * ij[0]
def layer_vars(letter, k, lo, hi): return [f"{letter}_{i}_{2*i-k}" for i in range(lo, hi + 1)]
# unknown layers per E_n (n = 2..-2): (A_{n-3}, B_{n-2}) paired with (B_3, A_2)
spec = {2: ("b", 0, 1, 12, "a", -1, 0, 7), 1: ("a", -2, 0, 6, "b", -1, 0, 11), 0: ("a", -3, 0, 5, "b", -2, 0, 10),
        -1: ("a", -4, 0, 4, "b", -3, 0, 9), -2: ("a", -5, 0, 3, "b", -4, 0, 8)}
def rank(M, ncols):
    M = [r[:] for r in M]; r = 0
    for c in range(ncols):
        i = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if i is None: continue
        M[r], M[i] = M[i], M[r]; iv = inv(M[r][c]); M[r] = [(x * iv) % Rr for x in M[r]]
        for j in range(len(M)):
            if j != r and M[j][c] != 0:
                f = M[j][c]; M[j] = [(M[j][l] - f * M[r][l]) % Rr for l in range(ncols)]
        r += 1
    return r
out = {}
for n, (l1, k1, lo1, hi1, l2, k2, lo2, hi2) in spec.items():
    U = layer_vars(l1, k1, lo1, hi1) + layer_vars(l2, k2, lo2, hi2)
    W = 1 - n
    rows = sorted(k for k in eqsc if wt(k) == W)
    idx = {u: i for i, u in enumerate(U)}
    M = []
    for k in rows:
        row = [ZERO] * len(U)
        for c, pv, qv in eqsc[k]:
            for a, b in ((pv, qv), (qv, pv)):
                if a in idx and b in top:
                    row[idx[a]] = (row[idx[a]] + c * top[b]) % Rr
        M.append(row)
    pure = [rows[i] for i, r in enumerate(M) if all(x == 0 for x in r)]
    Mop = [r for r in M if any(x != 0 for x in r)]
    rk = rank(Mop, len(U))
    print(f"E_{n}: block {len(M)} rows, operator {len(Mop)}x{len(U)}, rank {rk}, left nullity {len(Mop)-rk}, "
          f"kernel dim {len(U)-rk}; pure-condition rows (monomial x^i y^j): {pure}")
    out[n] = dict(unknowns=U, rows=[list(r) for r in rows], pure=[list(p) for p in pure], rank=rk)
json.dump(out, open(os.path.join(HERE, "ops_c.json"), "w"))
