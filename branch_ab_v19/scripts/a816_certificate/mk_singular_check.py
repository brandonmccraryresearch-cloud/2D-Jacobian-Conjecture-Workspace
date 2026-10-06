"""mk_singular_check.py CERT.json OUT.sing OUTLIFT -- Singular script (char 0, Q(w)) that rebuilds the 75 generators with
the verbatim lines of the read-only repository file a816_full.sing, loads the 76 cofactors of CERT.json, checks
sum_k I2[k]*T[k] == 1 exactly, and writes the cofactors in Singular's own string format to OUTLIFT (76 lines, the order
of I2 = I + (a_8_16*z - 1), i.e. the format targeted by CAIC's a816_full_lift.sing)."""
import os
import sys, json
from fractions import Fraction
SRC = os.environ.get("A816_SRC", os.path.join(os.path.dirname(os.path.abspath(__file__)), "a816_full.sing"))   # copy of scripts/a816_full.sing (md5 aa68d2ff...)
cert_path, out, outlift = sys.argv[1], sys.argv[2], sys.argv[3]
cert = json.load(open(cert_path))
names = cert["vars"]                      # 53 unknowns + z
lines = open(SRC).read().split("\n")
ring = [l for l in lines if l.startswith("ring r =")][0]
i0 = next(i for i, l in enumerate(lines) if l.startswith("minpoly")); i1 = next(i for i, l in enumerate(lines) if l.startswith("I = simplify(I, 2);"))
def coef(q):
    parts = []
    for k, s in enumerate(q):
        fr = Fraction(s)
        if fr == 0: continue
        parts.append(f"({fr})" + ("" if k == 0 else ("*w" if k == 1 else f"*w^{k}")))
    return "(" + "+".join(parts) + ")" if parts else "0"
def mono(e):
    f = [f"{names[i]}^{p}" if p > 1 else names[i] for i, p in enumerate(e) if p]
    return "*".join(f) if f else "1"
body = [ring] + lines[i0:i1 + 1] + ['if (size(I) != 75) { "ERROR: expected 75 generators"; quit; }',
        "ideal I2 = I + ideal(a_8_16*z - 1);", "matrix T[76][1];"]
for r in range(1, 77):
    terms = cert["rows"].get(str(r), [])
    s = "+".join(f"{coef(q)}*{mono(e)}" for e, q in terms if any(Fraction(x) != 0 for x in q)) or "0"
    body.append(f"T[{r},1] = {s};")
body += ['system("--ticks-per-sec", 1000); int t0 = rtimer;',
         "poly chk = 0; int k; for (k = 1; k <= 76; k++) { chk = chk + I2[k]*T[k,1]; }",
         '"check ms:"; rtimer - t0;',
         'if (chk == 1) { "SINGULAR CHECK: sum_k I2[k]*T[k] == 1 over Q(w): VALID"; } else { "SINGULAR CHECK: FAILED"; size(chk); }',
         f'link ll = ":w {outlift}";',
         "for (k = 1; k <= 76; k++) { write(ll, string(T[k,1])); }", "close(ll);",
         f'"wrote {outlift}";', "quit;"]
open(out, "w").write("\n".join(body) + "\n")
print("wrote", out)
