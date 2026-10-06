"""build_matrix.py -- the branch-(c) weighted Macaulay matrix M_W modulo p, as sparse columns.

Generators.  F_n (n = Psi, Phi1, Phi2, Theta1, Theta2, Theta3) in K5[t, s, r, u, q], from the v3.1 bundle's own code,
imported read-only (bundle_v3_1/jacobian_lean/chart_certificates/step3b_rank_lift.py, step1/lowerc_chart.py):
conds_c.json on the chart T2 = 1, S2 = kappa.  As in step3b_rank_lift.py, two derivations of the reduced generators
are compared (exact K5 substitution, then reduction; reduction, then substitution) and must agree.
Matrix (step3b_rank_lift.macaulay, re-implemented):
  columns  (n, m) for every monomial m in t s r u q with wdeg(m) <= W - wt(F_n), weights 1 2 3 3 4, wt = 5 6 6 7 7 7;
  rows     the monomials of the K5 supports of the products m * F_n, plus the monomial 1;
  entries  the K5 coefficients reduced at w = w0 modulo p.
Output: a pickle {"p", "w0", "W", "rows", "cols", "colv"}, colv[j] = [(row index, entry mod p), ...] (nonzero entries).
usage: python3 build_matrix.py CHART_CERTIFICATES_DIR p w0 OUT.pkl [W]      (needs python-flint, numpy)
"""
import sys, os, time, pickle, hashlib

CH, p, w0, OUT = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
W = int(sys.argv[5]) if len(sys.argv) > 5 else 24
sys.set_int_max_str_digits(0)
sys.path.insert(0, CH)
sys.path.insert(0, os.path.join(CH, "step1"))
import step3b_rank_lift as S                     # read-only; run with PYTHONDONTWRITEBYTECODE=1

t0 = time.time()
C7 = S.load7()
kap = S.kappa(C7)
ch = S.chart(C7, kap)
red = S.reducer(p, w0)                           # asserts R(w0) = 0 mod p and p-integrality of every coefficient
G = {n: {m: red(c) for m, c in ch[n].items()} for n in S.NAMES}
Gd = S.chart_modp_direct(p, w0)
same = all({m: c for m, c in G[n].items() if c} == Gd[n] for n in S.NAMES)
assert same, "the two derivations of the reduced chart generators disagree"
print(f"p = {p}, w0 = {w0}: R(w0) = 0 mod p and every coefficient p-integral (asserted); generators on the chart, "
      f"K5 terms {dict((n, len(ch[n])) for n in S.NAMES)}, nonzero mod p "
      f"{dict((n, sum(1 for c in G[n].values() if c)) for n in S.NAMES)}; two derivations agree: {same}")
cols = [(n, m) for n in S.NAMES for m in S.monos_upto(W - S.WTF[n])]
rowset = {}
for n, m in cols:
    for mm in G[n]:                              # K5 support, including coefficients that vanish mod p
        rowset.setdefault(tuple(a + b for a, b in zip(m, mm)), None)
rowset.setdefault((0, 0, 0, 0, 0), None)
rows = list(rowset)
ridx = {r: i for i, r in enumerate(rows)}
colv = [[(ridx[tuple(a + b for a, b in zip(m, mm))], c) for mm, c in G[n].items() if c] for n, m in cols]
nnz = sum(len(c) for c in colv)
percol = {n: sum(1 for nn, _ in cols if nn == n) for n in S.NAMES}
h = hashlib.sha256(repr((rows, cols, colv)).encode()).hexdigest()
print(f"W = {W}: {len(rows)} rows x {len(cols)} columns (per generator {percol}), {nnz} nonzero entries; "
      f"sha256 of (rows, cols, entries) {h[:16]} ({time.time() - t0:.1f} s)")
pickle.dump({"p": p, "w0": w0, "W": W, "rows": rows, "cols": cols, "colv": colv}, open(OUT, "wb"))
