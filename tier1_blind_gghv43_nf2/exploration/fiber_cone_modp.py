"""
fiber_modp.py -- EXPLORATION ONLY (mod p).
Normalisation a_1_0 = b_2_1 = a_8_14 = a_8_16 = 1 (valid over an alg. closed field: the
4x4 log-weight matrix of (P-scale, Q-scale, x-scale, y-scale) on these four vertex
coefficients has determinant 14).
Step 1: lex GB of the weight -4 block (shape position in a_2_2), factor the eliminant.
Step 2: for each irreducible factor f (theta = one root; covers its whole Frobenius orbit),
        adjoin v - h_v(theta) for every weight -4 variable v and the weight -3..0 equations,
        over F_p(theta); compute std; report whether 1 is in the ideal, else dim.
usage: python3 fiber_modp.py p [maxdeg] [blocks]    blocks default "-3,-2,-1,0"
"""
import subprocess, sys
from gen_system import build

p = int(sys.argv[1])
maxdeg = int(sys.argv[2]) if len(sys.argv) > 2 else 6
useb = [int(s) for s in sys.argv[3].split(",")] if len(sys.argv) > 3 else [-3, -2, -1, 0]
LP, LQ, eqs, tgt = build()
w = lambda ij: ij[1] - 2 * ij[0]
vw = lambda v: w(tuple(map(int, v.split('_')[1:])))
key = lambda v: (v[0], int(v.split('_')[1]), int(v.split('_')[2]))
norm = {"a_1_0", "b_2_1", "a_8_14"}
tok = lambda v: "1" if v in norm else v

blocks = {}
for k in sorted(eqs):
    s = "+".join(f"({c})*{tok(pv)}*{tok(qv)}" for c, pv, qv in eqs[k])
    if k == tgt:
        s += "-lam"
    blocks.setdefault(w(k), []).append(s)

allvars = sorted({v for T in eqs.values() for c, pv, qv in T for v in (pv, qv)} - norm, key=key)
e5vars = [v for v in allvars if (v[0] == 'a' and vw(v) == -2) or (v[0] == 'b' and vw(v) == -3)]
restvars = [v for v in allvars if v not in e5vars]
lexvars = [v for v in e5vars if v != "a_2_2"] + ["lam", "a_2_2"]
evars = restvars + [v for v in e5vars if v != "a_2_2"] + ["lam"]
restpolys = ",".join(s for b in useb for s in blocks[b])

S = f"""
ring L = {p}, ({','.join(lexvars)}), lp;
ideal I = {','.join(blocks[-4])};
ideal G = stdfglm(I);
"E5: size lex GB", size(G), " deg eliminant", deg(G[1]);
list F = factorize(G[1]);
int i, j; string fs, hs;
for (i=1; i<=size(F[1]); i++) {{
  if (deg(F[1][i]) > 0 and deg(F[1][i]) <= {maxdeg}) {{
    fs = string(F[1][i]);
    hs = "";
    for (j=1; j<=nvars(L)-1; j++) {{ hs = hs + "," + string(var(j)) + "-(" + string(reduce(var(j), G)) + ")"; }}
    "---- factor", i, "degree", deg(F[1][i]), "mult", F[2][i];
    execute("ring E = (" + string({p}) + ", a_2_2), ({','.join(evars)}), dp;");
    execute("minpoly = " + fs + ";");
    execute("ideal J = {restpolys}" + hs + ";");
    int t0 = timer;
    ideal GJ = std(J);
    "   rest: size std", size(GJ), " dim", dim(GJ), " vdim", vdim(GJ), " time", timer - t0;
    if (size(GJ) <= 3) {{ GJ; }}
    setring L;
    kill E;
  }}
}}
quit;
"""

if __name__ == "__main__":
    r = subprocess.run(["Singular", "-q"], input=S, capture_output=True, text=True, timeout=5000)
    print(r.stdout[-6000:])
    print(r.stderr[-3000:])
