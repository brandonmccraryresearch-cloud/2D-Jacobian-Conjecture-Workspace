"""phi_stage6_vs_6b.py DIR -- exact cross-check of the E0 fix (run on final/ or fixed/).
Stage 6 now solves E0 by projecting with the left null vector of M0; stages 6b and 6e drop a dependent row.
Both are valid on Psi = 0, so their Phi must differ by multiples of Psi.  Checks, exactly over K5, that
Phi_i(stage 6) - Phi_i(stage 6b) = Psi * (a_i t1 + b_i t2).  Needs BRANCH_C_CERTGEN, BRANCH_C_WORKDIR, SINGULAR."""
import runpy, os, sys, io, contextlib, itertools
from flint import fmpq_poly
base = sys.argv[1]
def run(path):
    with contextlib.redirect_stdout(io.StringIO()):
        return runpy.run_path(path, run_name="__main__")
g6 = run(os.path.join(base, "branch_c_stage6_e_minus1_obstruction.py"))
g6b = run(os.path.join(base, "branch_c_stage6b_phi12.py"))
g6e = run(os.path.join(base, "branch_c_stage6e_patch101.py"))
Rr = fmpq_poly([26, 0, 3, 3, -1, 1]); Z = fmpq_poly([0])
def inv(a):
    g, s, _ = a.xgcd(Rr); assert g == 1; return s % Rr
Psi = g6e["Psi"]
def shift(m, i): return tuple(e + (1 if j == i else 0) for j, e in enumerate(m))
for i in range(2):
    A, B = g6["Phi"][i], g6b["Phi"][i]
    D = {m: (A.get(m, Z) - B.get(m, Z)) % Rr for m in set(A) | set(B)}
    D = {m: v for m, v in D.items() if v != 0}
    # D = Psi * (a t1 + b t2) ?  columns: Psi*t1, Psi*t2
    c1 = {shift(m, 0): v for m, v in Psi.items()}; c2 = {shift(m, 1): v for m, v in Psi.items()}
    mons = sorted(set(D) | set(c1) | set(c2))
    sol = None
    for m1, m2 in itertools.combinations(mons, 2):
        p, q, r, s = c1.get(m1, Z), c2.get(m1, Z), c1.get(m2, Z), c2.get(m2, Z)
        det = (p * s - q * r) % Rr
        if det == 0: continue
        di = inv(det); y1, y2 = D.get(m1, Z), D.get(m2, Z)
        sol = (((y1 * s - q * y2) * di) % Rr, ((p * y2 - r * y1) * di) % Rr); break
    a, b = sol
    ok = all((D.get(m, Z) - a * c1.get(m, Z) - b * c2.get(m, Z)) % Rr == 0 for m in mons)
    print(f"Phi_{i+1}: stage6 - stage6b ({len(D)} terms) == Psi*(a*t1 + b*t2) exactly over K5: {ok}")
