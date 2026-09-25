"""
cert_fibers_m2.py -- independent Macaulay2 re-implementation of certificate step M.
Same mathematics as cert_fibers_singular.py, different GB engine:
 (M1) I5 (weight -4 block, a_1_0 = b_2_1 = a_8_14 = 1) over ZZ/p, Lex GB, check shape position
      in a_2_2, factor the eliminant.
 (M2) for each irreducible factor f: coefficient field K = toField(ZZ/p[th]/(f)); fibre ideal J
      (weights -3..0 + pins v - h_v(th)); check u^4 % gb(J) == 0 for all 51 weight>=-1 variables u.
usage: python3 cert_fibers_m2.py p
"""
import subprocess, sys, re
from gen_system import build

p = int(sys.argv[1])
LP, LQ, eqs, tgt = build()
w = lambda ij: ij[1] - 2 * ij[0]
vw = lambda v: w(tuple(map(int, v.split('_')[1:])))
key = lambda v: (v[0], int(v.split('_')[1]), int(v.split('_')[2]))
ren = lambda t: re.sub(r'\b([ab])_(\d+)_(\d+)\b', r'\1\2y\3', t)
norm = {"a_1_0", "b_2_1", "a_8_14"}
tok = lambda v: "1" if v in norm else v
blocks = {}
for k in sorted(eqs):
    s = "+".join(f"({c})*{tok(pv)}*{tok(qv)}" for c, pv, qv in eqs[k])
    if k == tgt:
        s += "-lam"
    blocks.setdefault(w(k), []).append(ren(s))
allvars = sorted({v for T in eqs.values() for c, pv, qv in T for v in (pv, qv)} - norm, key=key)
e5 = [ren(v) for v in allvars if (v[0] == 'a' and vw(v) == -2) or (v[0] == 'b' and vw(v) == -3)]
rest = [ren(v) for v in allvars if ren(v) not in e5]
assert len(rest) == 51 and len(e5) == 16
lexvars = [v for v in e5 if v != "a2y2"] + ["lam", "a2y2"]
evars = rest + [v for v in e5 if v != "a2y2"] + ["lam"]

M = f"""
nfail = 0;
kk = ZZ/{p};
needsPackage "FGLM";
L0 = kk[{','.join(lexvars)}, MonomialOrder => GRevLex];
I50 = ideal({','.join(blocks[-4])});
gb I50;
L = kk[{','.join(lexvars)}, MonomialOrder => Lex];
G = flatten entries gens fglm(I50, L);
-- shape position: exactly one element per variable, leading monomials = the variables / a2y2^d
lms = apply(G, g -> leadMonomial g);
elim = select(G, g -> support g == {{a2y2}});
if #G != numgens L or #elim != 1 then (print "FAIL shape"; nfail = nfail + 1);
m = first elim;
print("eliminant degree " | toString(first degree m));
H = apply(drop(gens L, -1), v -> v % (ideal G));   -- h_v(a2y2)
if not all(H, h -> isSubset(support h, {{a2y2}})) then (print "FAIL shape tails"; nfail = nfail + 1);
S1 = kk[th];
mS = sub(m, {{a2y2 => th}} | apply(drop(gens L, -1), v -> v => 0));
facs = apply(toList factor mS, f -> (value f#0, f#1));
facs = select(facs, f -> first degree(f#0) > 0);
tot = sum apply(facs, f -> (first degree f#0) * f#1);
print("sum of factor degrees " | toString tot);
if tot != first degree m then (print "FAIL factor degrees"; nfail = nfail + 1);
restN = {len(rest)};
for f in facs do (
  Kq := toField(S1 / ideal(f#0));
  E := Kq[{','.join(evars)}, MonomialOrder => GRevLex];
  thK := sub(th, Kq);
  pins := apply(#H, i -> (gens E)#({len(rest)} + i) - sub(sub(H#i, {{a2y2 => th}} | apply(drop(gens L, -1), v -> v => 0)), Kq));
  J := ideal({','.join(blocks[-3] + blocks[-2] + blocks[-1] + blocks[0]).replace('a2y2', 'thK')}) + ideal(pins);
  GJ := gb J;
  okAll := all(take(gens E, restN), u -> (u^4) % GJ == 0);
  print("fibre factor deg " | toString(first degree f#0) | " mult " | toString(f#1) | ": dim " | toString(dim J) | " degree " | toString(degree J) | " all u^4 in J: " | toString okAll);
  if not okAll then (print "FAIL fibre"; nfail = nfail + 1);
);
print("NFAIL " | toString nfail);
exit 0;
"""

if __name__ == "__main__":
    open(f"cert_fibers_m2_p{p}.m2", "w").write(M)
    r = subprocess.run(["M2", "--script", f"cert_fibers_m2_p{p}.m2"], capture_output=True, text=True, timeout=20000)
    out = r.stdout + r.stderr
    print(out[-5000:])
    bad = any(l.strip().startswith("FAIL") for l in out.splitlines()) or ("NFAIL 0" not in out) or ("error" in out)
    print("OVERALL:", "FAIL" if bad else "PASS", "p =", p)
    sys.exit(1 if bad else 0)
