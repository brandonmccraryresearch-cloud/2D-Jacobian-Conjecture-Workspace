"""mk_lift.py CHAR MODE OUT.sing -- build a Singular script from the repository's a816_full.sing (read-only source)
that sets up the same 75 generators (layers d = 0..3 of J = [P,Q] - x^2 at the K5 point), adds the Rabinowitsch
generator a_8_16*z - 1 and computes a representation of 1.
  CHAR : 0 (over Q(w)) or a prime p at which R is irreducible (then (p,w)+minpoly is F_{p^5})
  MODE : lift | liftstd
The script prints timings, certificate statistics, an exact in-ring check matrix(I2)*T == 1, and writes the
generators and the certificate to files (gens_<CHAR>.txt, cert_<MODE>_<CHAR>.txt) when asked (WRITE=1)."""
import sys, re, os
SRC = os.environ.get("A816_SRC", os.path.join(os.path.dirname(os.path.abspath(__file__)), "a816_full.sing"))   # copy of scripts/a816_full.sing (md5 aa68d2ff...)
char, mode, out = sys.argv[1], sys.argv[2], sys.argv[3]
write = os.environ.get("WRITE", "0") == "1"
lines = open(SRC).read().split("\n")
ring = [l for l in lines if l.startswith("ring r =")][0]
assert ring.startswith("ring r = (0,w),")
ring = ring.replace("ring r = (0,w),", f"ring r = ({char},w),", 1)
i0 = next(i for i, l in enumerate(lines) if l.startswith("minpoly"))
i1 = next(i for i, l in enumerate(lines) if l.startswith("I = simplify(I, 2);"))
keep = lines[i0:i1 + 1]                     # minpoly, P, Q, J, the layer loop (d = 0..3), simplify -- verbatim
assert [k[:8] for k in keep] == ["minpoly ", "poly P =", "poly Q =", "poly J =", "ideal I;", "for (k =", "I = simp"], [k[:8] for k in keep]
body = [ring] + keep + ["if (size(I) != 75) { \"ERROR: expected 75 generators\"; quit; }",
  "ideal I2 = I + ideal(a_8_16*z - 1);",
  "system(\"--ticks-per-sec\", 1000); int t0 = rtimer;"]
if mode == "lift":
    body += ["matrix T = lift(I2, ideal(1));"]
elif mode == "liftstd":
    body += ["matrix T; ideal G = liftstd(I2, T); \"liftstd basis:\"; G;",
             "if (!(size(G) == 1 && G[1] == 1)) { \"NOT UNIT\"; quit; }"]
body += ["\"time ms:\"; rtimer - t0;",
  "int i; int tot = 0; int mx = 0; int md = 0;",
  "for (i = 1; i <= nrows(T); i++) { tot = tot + size(T[i,ncols(T)]); if (size(T[i,ncols(T)]) > mx) { mx = size(T[i,ncols(T)]); } if (deg(T[i,ncols(T)]) > md) { md = deg(T[i,ncols(T)]); } }",
  "\"cofactors:\"; nrows(T); \"total terms:\"; tot; \"max terms in one cofactor:\"; mx; \"max total degree:\"; md;",
  "int t1 = rtimer; poly chk = 0; for (i = 1; i <= nrows(T); i++) { chk = chk + I2[i]*T[i,ncols(T)]; }",
  "\"check sum_i I2[i]*T[i] == 1:\"; chk == 1; \"check time ms:\"; rtimer - t1;"]
if write:
    body += [f"write(\":w gens_{char}.txt\", string(I2));",
             "string s; for (i = 1; i <= nrows(T); i++) { s = string(T[i,ncols(T)]); write(\":a cert_" + mode + "_" + char + ".txt\", s); }"]
body += ["quit;"]
open(out, "w").write("\n".join(body) + "\n")
print("wrote", out)
