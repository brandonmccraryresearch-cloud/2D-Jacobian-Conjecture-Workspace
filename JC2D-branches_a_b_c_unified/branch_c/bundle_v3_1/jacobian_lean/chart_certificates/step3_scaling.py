"""Height of the canonical K5 certificate vs. rank: the slice t1 = 0 of lower_c's chart ideal, cofactor degree D = 2, 3, 4.
(canonical = pivot columns / independent rows from a mod-p RREF, free unknowns 0, exact FLINT solve)."""
import sys, os, time
sys.path.insert(0, os.path.abspath(".")); sys.path.insert(0, os.path.abspath("step1"))
from lowerc_chart import *
from certlin import build, modp_consistent
from exactsolve import canonical_solve, cofactors_from, verify, height
C7 = load7(); kap = kappa(C7); B = chart(C7, kap, t1=Z)
gens = [B[n] for n in NAMES]; one = {(0, 0, 0, 0): fmpq_poly([1])}
for D in [int(x) for x in sys.argv[1:]]:
    t = time.time()
    cols, cps, rows, ridx, rhs = build(gens, [D] * 6, one, 4)
    sol = canonical_solve(cols, cps, rows, ridx, rhs, verbose=True)
    cof = cofactors_from(sol, cols, 6)
    ok = verify(cof, gens, one)
    nz = sum(len(c) for c in cof); H = height(cof)
    tot = sum(len(str(c.p)) + len(str(c.q)) for ci in cof for v in ci.values() for c in list(v))
    print(f"D={D}: system {len(rows)}x{len(cols)}, nonzero K5-terms {nz}, max height {H} digits, total digits {tot}, "
          f"exact check {ok}, {time.time()-t:.0f}s", flush=True)
