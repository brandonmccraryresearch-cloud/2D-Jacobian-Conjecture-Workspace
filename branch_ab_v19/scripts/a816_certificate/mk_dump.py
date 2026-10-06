"""mk_dump.py CHAR WHAT OUT.sing -- Singular script (system lines copied verbatim from the read-only repository file
branch_ab_v17/scripts/a816_full.sing) that dumps, term by term, either
  WHAT=gens : the 76 generators of I2 = I + (a_8_16*z - 1) and the (i,j) label of each J-coefficient generator
  WHAT=cert : the liftstd certificate T (76 x 1) with sum_k I2[k]*T[k,1] = 1, after an in-ring check
Line format: k|e_1,...,e_56|coefficient   (coefficient printed by Singular as an element of CHAR(w)/(R))."""
import os
import sys
SRC = os.environ.get("A816_SRC", os.path.join(os.path.dirname(os.path.abspath(__file__)), "a816_full.sing"))   # copy of scripts/a816_full.sing (md5 aa68d2ff...)
char, what, out = sys.argv[1], sys.argv[2], sys.argv[3]
lines = open(SRC).read().split("\n")
ring = [l for l in lines if l.startswith("ring r =")][0]
assert ring.startswith("ring r = (0,w),")
ring = ring.replace("ring r = (0,w),", f"ring r = ({char},w),", 1)
i0 = next(i for i, l in enumerate(lines) if l.startswith("minpoly"))
i1 = next(i for i, l in enumerate(lines) if l.startswith("I = simplify(I, 2);"))
keep = lines[i0:i1 + 1]
assert [k[:8] for k in keep] == ["minpoly ", "poly P =", "poly Q =", "poly J =", "ideal I;", "for (k =", "I = simp"]
tag = f"{what}_{char}"
body = [ring] + keep + [
 'if (size(I) != 75) { "ERROR: expected 75 generators"; quit; }',
 'ideal I2 = I + ideal(a_8_16*z - 1);',
 'int ii; int jj; poly ff; poly tt; string ln;',
 f'write(":w {tag}.txt", "# char {char}");']
if what == "gens":
    body += [
     'list labs; int kk; intvec ee; int dd;',
     'for (kk = 1; kk <= ncols(C); kk++) { ee = leadexp(C[1,kk]); dd = 2*ee[nvars(basering)-1] - ee[nvars(basering)]; '
     'if ((dd >= 0) && (dd <= 3) && (C[2,kk] != 0)) { labs = labs + list(string(ee[nvars(basering)-1]) + "," + string(ee[nvars(basering)])); } }',
     'if (size(labs) != 75) { "ERROR: label count"; quit; }',
     f'for (ii = 1; ii <= 75; ii++) {{ write(":a {tag}.txt", "L|" + string(ii) + "|" + labs[ii]); }}',
     f'write(":a {tag}.txt", "V|" + varstr(basering));',
     'matrix TT[76][1]; for (ii = 1; ii <= 76; ii++) { TT[ii,1] = I2[ii]; }']
else:
    body += [
     'system("--ticks-per-sec", 1000); int t0 = rtimer;',
     'matrix T; ideal G = liftstd(I2, T);',
     'if (!(size(G) == 1 && G[1] == 1)) { "ERROR: liftstd basis is not {1}"; quit; }',
     '"liftstd ms:"; rtimer - t0;',
     'poly chk = 0; for (ii = 1; ii <= 76; ii++) { chk = chk + I2[ii]*T[ii,1]; }',
     'if (chk != 1) { "ERROR: in-ring check failed"; quit; }',
     '"in-ring check: sum I2[k]*T[k] == 1";',
     'matrix TT = T;']
body += [
 f'for (ii = 1; ii <= 76; ii++) {{ ff = TT[ii,1]; for (jj = 1; jj <= size(ff); jj++) {{ tt = ff[jj]; '
 f'write(":a {tag}.txt", string(ii) + "|" + string(leadexp(tt)) + "|" + string(leadcoef(tt))); }} }}',
 f'"DONE {tag}";', 'quit;']
open(out, "w").write("\n".join(body) + "\n")
