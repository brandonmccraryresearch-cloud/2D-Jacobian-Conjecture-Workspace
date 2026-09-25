"""
e5_modp.py -- EXPLORATION ONLY (mod p).
Solve the weight -4 block with normalisation a_1_0 = b_2_1 = a_2_2 = 1 and z*a_8_14 = 1,
over F_p, for a list of primes; report the factorisation pattern of the eliminant in a_8_14.
"""
import subprocess, sys, os
from gen_system import build

LP, LQ, eqs, tgt = build()
w = lambda ij: ij[1] - 2 * ij[0]
norm = {"a_1_0", "b_2_1", "a_2_2"}
tok = lambda v: "1" if v in norm else v
polys, used = [], set()
for key in sorted(eqs):
    if w(key) != -4:
        continue
    terms = [f"({c})*{tok(p)}*{tok(q)}" for c, p, q in eqs[key]]
    for c, p, q in eqs[key]:
        used |= {p, q}
    s = "+".join(terms)
    if key == tgt:
        s += "-lam"
    polys.append(s)
used = sorted(used - norm, key=lambda v: (v[0], int(v.split('_')[1]), int(v.split('_')[2])))
polys.append("z*a_8_14-1")
lexvars = [v for v in used if v != "a_8_14"] + ["z", "lam", "a_8_14"]


def script(p):
    return f"""
ring L = {p}, ({','.join(lexvars)}), lp;
ideal I = {','.join(polys)};
ideal G = stdfglm(I);
"NGB"; size(G); "DEG"; deg(G[1]);
list F = factorize(G[1]); int i; string s = "";
for (i=1; i<=size(F[1]); i++) {{ if (deg(F[1][i])>0) {{ s = s + string(deg(F[1][i])) + "^" + string(F[2][i]) + " "; }} }}
"PAT"; s;
quit;
"""


if __name__ == "__main__":
    primes = [int(a) for a in sys.argv[1:]]
    for p in primes:
        r = subprocess.run(["Singular", "-q"], input=script(p), capture_output=True, text=True, timeout=600)
        print(p, " ".join(r.stdout.split()))
