"""
mk_full.py -- full normalised system (all weights) in Singular syntax, with a block order
(dp on weight>=-1 variables, then dp on weight -2/-3 variables, then lam).
Normalisation: a_1_0 = b_2_1 = a_8_14 = a_8_16 = 1.
usage: python3 mk_full.py CHAR OUT.sing [extra-norm-list]
"""
import sys
from gen_system import build

char = sys.argv[1]
out = sys.argv[2]
LP, LQ, eqs, tgt = build()
w = lambda ij: ij[1] - 2 * ij[0]
vw = lambda v: w(tuple(map(int, v.split('_')[1:])))
key = lambda v: (v[0], int(v.split('_')[1]), int(v.split('_')[2]))
norm = {"a_1_0", "b_2_1", "a_8_14", "a_8_16"}
tok = lambda v: "1" if v in norm else v
polys = []
for k in sorted(eqs):
    s = "+".join(f"({c})*{tok(pv)}*{tok(qv)}" for c, pv, qv in eqs[k])
    if k == tgt:
        s += "-lam"
    polys.append(s)
allvars = sorted({v for T in eqs.values() for c, pv, qv in T for v in (pv, qv)} - norm, key=key)
e5 = [v for v in allvars if (v[0] == 'a' and vw(v) == -2) or (v[0] == 'b' and vw(v) == -3)]
rest = [v for v in allvars if v not in e5]
with open(out, "w") as f:
    f.write(f"ring R = {char}, ({','.join(rest)},{','.join(e5)},lam), (dp({len(rest)}),dp({len(e5)+1}));\n")
    f.write("ideal I =\n  " + ",\n  ".join(polys) + ";\n")
print(len(polys), "polys;", len(rest), "rest vars;", len(e5) + 1, "E5 vars incl lam")
