"""Exact K5 certificate for lower_c's ideal on the slice t1 = 0 of the chart (T2 = 1, S2 = kappa):
   1 = sum_i L_i * F_i in K5[s, r, u, q]  (s, r, u, q = S1, R1, R2, Q).
   Canonical solution: minimal uniform cofactor degree D, pivots from a mod-p RREF, free unknowns = 0, exact FLINT solve."""
import sys, os, json, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, ".."))
from lowerc_chart import *
from certlin import build, modp_consistent
from exactsolve import canonical_solve, cofactors_from, verify, height
C7 = load7(); kap = kappa(C7)
B = chart(C7, kap, t1=Z)
gens = [B[n] for n in NAMES]
one = {(0, 0, 0, 0): fmpq_poly([1])}
for D in range(1, 6):
    cols, cps, rows, ridx, rhs = build(gens, [D] * 6, one, 4)
    ra, rab = modp_consistent(cols, cps, rows, ridx, rhs, 1000003)
    print(f"D={D}: {len(rows)} x {len(cols)}, rank mod p {ra}, augmented {rab} -> {'consistent' if ra == rab else 'inconsistent'}", flush=True)
    if ra == rab: break
t = time.time()
sol = canonical_solve(cols, cps, rows, ridx, rhs)
cof = cofactors_from(sol, cols, 6)
ok = verify(cof, gens, one)
print(f"certificate: D = {D}, {sum(len(c) for c in cof)} K5-terms, max rational height {height(cof)} digits, "
      f"exact K5 check (same code path): {ok}  ({time.time()-t:.1f}s)")
json.dump({"slice": "chart T2 = 1, S2 = kappa (double root of Omega), T1 = 0; variables (S1, R1, R2, Q)",
           "generators": NAMES, "source": "certgen_c/conds_c.json (lower_c)", "degree": D,
           "cofactors": [[[list(m), [str(c) for c in list(v)]] for m, v in ci.items()] for ci in cof]},
          open(os.path.join(HERE, "certB_lowerc.json"), "w"))
