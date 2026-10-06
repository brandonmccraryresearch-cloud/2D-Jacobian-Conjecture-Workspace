"""mk_check_lift.py LIFT.txt OUT.sing -- Singular script (char 0, Q(w)) that rebuilds the 75 generators from the verbatim
lines of the read-only repository file branch_ab_v17/scripts/a816_full.sing, reads the 76 cofactor lines of LIFT.txt
(Singular's own polynomial format, order of I2 = I + (a_8_16*z - 1)) and checks sum_k I2[k]*L[k] == 1 exactly."""
import os
import sys, re
SRC = os.environ.get("A816_SRC", os.path.join(os.path.dirname(os.path.abspath(__file__)), "a816_full.sing"))   # copy of scripts/a816_full.sing (md5 aa68d2ff...)
lift_path, out = sys.argv[1], sys.argv[2]
lines = open(SRC).read().split("\n")
ring = [l for l in lines if l.startswith("ring r =")][0]
i0 = next(i for i, l in enumerate(lines) if l.startswith("minpoly")); i1 = next(i for i, l in enumerate(lines) if l.startswith("I = simplify(I, 2);"))
lift = [l for l in open(lift_path).read().split("\n") if l.strip()]
assert len(lift) == 76 and all(re.fullmatch(r"[0-9a-z_*^+\-/() ]+", l) for l in lift)
body = [ring] + lines[i0:i1 + 1] + ['if (size(I) != 75) { "ERROR: expected 75 generators"; quit; }',
        "ideal I2 = I + ideal(a_8_16*z - 1);", "matrix L[76][1];"] + [f"L[{k + 1},1] = {l};" for k, l in enumerate(lift)] + [
        'system("--ticks-per-sec", 1000); int t0 = rtimer;',
        "poly chk = 0; int kk; for (kk = 1; kk <= 76; kk++) { chk = chk + I2[kk]*L[kk,1]; }",
        f'if (chk == 1) {{ "SINGULAR CHECK ({lift_path} with the repository generators): sum_k I2[k]*L[k] == 1 over Q(w): VALID"; }} else {{ "SINGULAR CHECK ({lift_path}): FAILED"; }}',
        '"check ms:"; rtimer - t0;', "quit;"]
open(out, "w").write("\n".join(body) + "\n")
print("wrote", out)
