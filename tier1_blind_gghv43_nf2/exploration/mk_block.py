"""
mk_block.py -- emit a Singular ring+ideal containing only the equations whose bracket
monomial has weight in a given set (w = j - 2i), restricted to the variables that occur.
usage: python3 mk_block.py CHAR WEIGHTS NORMALIZE OUT.sing     (WEIGHTS e.g. "-4" or "-4,-3")
"""
import sys
from gen_system import build

char = int(sys.argv[1])
Ws = [int(s) for s in sys.argv[2].split(",")]
norm = [] if sys.argv[3] == "none" else sys.argv[3].split(",")
out = sys.argv[4]
LP, LQ, eqs, tgt = build()
w = lambda ij: ij[1] - 2 * ij[0]
tok = lambda v: "1" if v in norm else v
polys, used = [], []
for key in sorted(eqs):
    if w(key) not in Ws:
        continue
    terms = []
    for c, p, q in eqs[key]:
        terms.append(f"({c})*{tok(p)}*{tok(q)}")
        for v in (p, q):
            if v not in norm and v not in used:
                used.append(v)
    s = "+".join(terms)
    if key == tgt:
        s += "-lam"
    polys.append(s)
order = lambda v: (v[0], int(v.split('_')[1]), int(v.split('_')[2]))
used = sorted(used, key=order)
with open(out, "w") as f:
    f.write(f"// block weights={Ws} norm={norm}\n")
    f.write(f"ring R = {char}, ({','.join(used + ['lam'])}), dp;\n")
    f.write("ideal I =\n  " + ",\n  ".join(polys) + ";\n")
print(len(polys), "equations,", len(used) + 1, "variables:", used)
