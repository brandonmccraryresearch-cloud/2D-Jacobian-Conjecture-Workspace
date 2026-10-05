"""mk_aux_sing.py -- writes the auxiliary Singular inputs used in the a_{8,16} work (system lines copied verbatim
from the read-only repository file branch_ab_v17/scripts/a816_full.sing):
  cmp_gens.sing        CAIC's a816_generators.txt == the repository ideal, entry by entry (char 0)
  probe_modp.sing      mod p (inert p): std(I), Krull dimension, a_8_16^k in I for k = 1..4
  lift_a2_modp.sing    mod p: lift(I, a_8_16^2) (the z-free certificate) with its in-ring check
  nilpotency_modp.sing mod p: x^ceil(4/depth) in I for each of the 51 unknowns
  check_roundtrip.sing CAIC's generator file + a816_lift.txt: 1 = sum f_i e_i + g (a_8_16 z - 1) (char 0)
usage: python3 mk_aux_sing.py [P]   (P = inert prime, default 536870813)"""
import os
import sys, re
from a816_system import NAMES, DEPTH
SRC = os.environ.get("A816_SRC", os.path.join(os.path.dirname(os.path.abspath(__file__)), "a816_full.sing"))   # copy of scripts/a816_full.sing (md5 aa68d2ff...)
P = sys.argv[1] if len(sys.argv) > 1 else "536870813"
lines = open(SRC).read().split("\n")
ring0 = [l for l in lines if l.startswith("ring r =")][0]
ringp = ring0.replace("ring r = (0,w),", f"ring r = ({P},w),", 1)
i0 = next(i for i, l in enumerate(lines) if l.startswith("minpoly")); i1 = next(i for i, l in enumerate(lines) if l.startswith("I = simplify(I, 2);"))
SYS = lines[i0:i1 + 1]
def write(name, body): open(name, "w").write("\n".join(body) + "\n")
gens = [l.strip() for l in open("caic_inputs/a816_generators.txt") if l.strip()]
lift = [l for l in open("a816_lift.txt").read().split("\n") if l.strip()]
assert all(re.fullmatch(r"[0-9a-z_*^+\-/() ]+", l) for l in gens + lift)
write("cmp_gens.sing", [ring0] + SYS + ["ideal Gc = " + ",\n".join(gens) + ";",
  '"repo size:"; size(I); "caic size:"; size(Gc);',
  'int bad = 0; int kk; for (kk = 1; kk <= 75; kk++) { if (I[kk] != Gc[kk]) { bad = bad + 1; "MISMATCH at"; kk; } }',
  '"entrywise mismatches:"; bad;', "quit;"])
write("probe_modp.sing", [ringp] + SYS + ['system("--ticks-per-sec", 1000); int t0 = rtimer;',
  'ideal SI = std(I); "std(I) ms:"; rtimer - t0; "size std(I):"; size(SI); "Krull dim (56 ring variables, 5 of them absent from I):"; dim(SI);',
  'int kk; for (kk = 1; kk <= 4; kk++) { "k ="; kk; "NF(a_8_16^k, std(I)) == 0:"; reduce(a_8_16^kk, SI) == 0; }', "quit;"])
write("lift_a2_modp.sing", [ringp] + SYS + ['system("--ticks-per-sec", 1000); int t0 = rtimer;',
  'matrix T = lift(I, ideal(a_8_16^2)); "lift(I, a^2) ms:"; rtimer - t0;',
  'int i; int tot = 0; int mx = 0; int md = 0; for (i = 1; i <= nrows(T); i++) { tot = tot + size(T[i,1]); if (size(T[i,1]) > mx) { mx = size(T[i,1]); } if (deg(T[i,1]) > md) { md = deg(T[i,1]); } }',
  '"terms:"; tot; "max terms:"; mx; "max deg:"; md;',
  'poly chk = 0; for (i = 1; i <= nrows(T); i++) { chk = chk + I[i]*T[i,1]; } "check == a^2:"; chk == a_8_16^2;', "quit;"])
body = [ringp] + SYS + ['system("--ticks-per-sec", 1000); int t0 = rtimer;', 'ideal SI = std(I);', 'int bad = 0; int good = 0;']
for n in NAMES:
    if n in ("a_0_0", "b_0_0"): continue
    k = {1: 4, 2: 2, 3: 2}[DEPTH[n]]
    body.append(f'if (reduce({n}^{k}, SI) == 0) {{ good++; }} else {{ bad++; "not in I: {n}^{k}"; }}')
write("nilpotency_modp.sing", body + ['"unknowns with x^ceil(4/depth) in I:"; good; "failures:"; bad; "ms:"; rtimer - t0;', "quit;"])
caic = open("caic_inputs/a816_full_lift.sing").read().split("\n")
ringc = [l for l in caic if l.startswith("ring r =")][0]; mp = [l for l in caic if l.startswith("minpoly")][0]
write("check_roundtrip.sing", [ringc, mp, "ideal E = " + ",\n".join(gens) + ";", "ideal Jr = E + ideal(a_8_16*z - 1);",
  "matrix L[76][1];"] + [f"L[{k+1},1] = {l};" for k, l in enumerate(lift)] + [
  "poly chk = 0; int k; for (k = 1; k <= 76; k++) { chk = chk + Jr[k]*L[k,1]; }",
  'if (chk == 1) { "ROUND TRIP (CAIC generators file + a816_lift.txt): 1 = sum f_i e_i + g (a_8_16 z - 1): VALID"; } else { "ROUND TRIP FAILED"; }',
  "quit;"])
print("wrote cmp_gens.sing probe_modp.sing lift_a2_modp.sing nilpotency_modp.sing check_roundtrip.sing")
