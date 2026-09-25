"""
e5_lex_modp.py -- EXPLORATION / candidate generation only.
Weight -4 block, normalisation a_1_0 = b_2_1 = a_8_14 = 1, lex GB mod p (shape position in
a_2_2).  Dumps the reduced lex GB as JSON {var: [coeffs of h_v(a_2_2)], '_elim': [...]}
(coefficient lists, lowest degree first, as integers mod p).
usage: python3 e5_lex_modp.py p out.json
"""
import subprocess, sys, json
from gen_system import build

p = int(sys.argv[1]); out = sys.argv[2]
LP, LQ, eqs, tgt = build()
w = lambda ij: ij[1] - 2 * ij[0]
vw = lambda v: w(tuple(map(int, v.split('_')[1:])))
key = lambda v: (v[0], int(v.split('_')[1]), int(v.split('_')[2]))
norm = {"a_1_0", "b_2_1", "a_8_14"}
tok = lambda v: "1" if v in norm else v
polys, used = [], set()
for k in sorted(eqs):
    if w(k) != -4:
        continue
    polys.append("+".join(f"({c})*{tok(pv)}*{tok(qv)}" for c, pv, qv in eqs[k]) + ("-lam" if k == tgt else ""))
    used |= {v for c, pv, qv in eqs[k] for v in (pv, qv)}
e5 = sorted(used - norm, key=key)
lexvars = [v for v in e5 if v != "a_2_2"] + ["lam", "a_2_2"]
S = f"""
ring L = {p}, ({','.join(lexvars)}), lp;
ideal I = {','.join(polys)};
ideal G = stdfglm(I);
int i, j; poly h;
"SIZE", size(G);
for (j=1; j<=nvars(L); j++) {{
  if (j < nvars(L)) {{ h = reduce(var(j), G); }} else {{ h = G[1]; }}
  string s = "COEF " + string(var(j));
  for (i=0; i<=deg(G[1]); i++) {{ s = s + " " + string(jet(h, i) - jet(h, i-1)) ; }}
  s;
  kill s;
}}
quit;
"""
r = subprocess.run(["Singular", "-q"], input=S, capture_output=True, text=True, timeout=3000)
res = {}
for line in r.stdout.splitlines():
    if line.startswith("COEF"):
        parts = line.split()
        v = parts[1]
        coeffs = []
        for d, term in enumerate(parts[2:]):
            # term is like c*a_2_2^d or 0
            if term == "0":
                coeffs.append(0)
                continue
            t = term.replace("a_2_2^%d" % d, "").replace("a_2_2", "").rstrip("*")
            coeffs.append(int(t) % p if t not in ("", "-") else (1 if t == "" else p - 1))
        res["_elim" if v == "a_2_2" else v] = coeffs
    elif line.startswith("SIZE"):
        print(line)
assert len(res) == len(lexvars), (len(res), r.stdout[-2000:], r.stderr[-2000:])
json.dump({"p": p, "data": res}, open(out, "w"))
el = res["_elim"]
print("p", p, "deg elim", max(i for i, c in enumerate(el) if c), "support", [i for i, c in enumerate(el) if c])
