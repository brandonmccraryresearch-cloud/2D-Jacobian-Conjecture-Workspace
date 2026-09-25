"""
cert_fibers_msolve.py -- third, independent engine (msolve F4) for the fibre claim, restricted to
F_p-rational points of V(I5 mod p).  Choose p with p != 1 mod 7 and m(a_2_2) having 5 linear
factors: then every mu_7-orbit of V(I5 mod p) has exactly one F_p-rational point (x -> x^7 is a
bijection of F_p), and the residual torus maps fibres over one orbit point isomorphically to the
others, so the 5 rational points represent all 35 points.
For each rational point xi and each weight>=-1 variable u: msolve on
   {weight -3..0 equations with xi substituted} + {u - 1}
must return [-1] (empty over F_p-bar).  By weighted homogeneity with positive weights this is
equivalent to u = 0 on the whole fibre.
The E5 points are obtained here WITHOUT Singular's factorisation: Singular provides the lex basis,
but the roots of the eliminant are found by python-flint (nmod_poly factor) and each point is
re-checked against the weight -4 equations in pure Python.
usage: python3 cert_fibers_msolve.py p
"""
import subprocess, sys, os, json
from flint import nmod_poly
from gen_system import build

p = int(sys.argv[1])
LP, LQ, eqs, tgt = build()
w = lambda ij: ij[1] - 2 * ij[0]
vw = lambda v: w(tuple(map(int, v.split('_')[1:])))
key = lambda v: (v[0], int(v.split('_')[1]), int(v.split('_')[2]))
norm = {"a_1_0": 1, "b_2_1": 1, "a_8_14": 1}
tok = lambda v: "1" if v in norm else v
allvars = sorted({v for T in eqs.values() for c, pv, qv in T for v in (pv, qv)} - set(norm), key=key)
e5 = [v for v in allvars if (v[0] == 'a' and vw(v) == -2) or (v[0] == 'b' and vw(v) == -3)]
rest = [v for v in allvars if v not in e5]
lexvars = [v for v in e5 if v != "a_2_2"] + ["lam", "a_2_2"]

# ---- lex basis from Singular, coefficients printed as lists
blk4 = ",".join("+".join(f"({c})*{tok(pv)}*{tok(qv)}" for c, pv, qv in eqs[k]) + ("-lam" if k == tgt else "")
                for k in sorted(eqs) if w(k) == -4)
S = f"""
ring L = {p}, ({','.join(lexvars)}), lp;
ideal I = {blk4};
ideal G = stdfglm(I);
int i, j; poly h;
for (j = 1; j <= nvars(L); j++) {{
  if (j < nvars(L)) {{ h = reduce(var(j), G); }} else {{ h = G[1]; }}
  string s = "COEF " + string(var(j));
  for (i = 0; i <= deg(G[1]); i++) {{ s = s + " " + string(leadcoef(jet(h, i) - jet(h, i-1) + 0)); }}
  s; kill s;
}}
quit;
"""
r = subprocess.run(["Singular", "-q", "--no-rc"], input=S, capture_output=True, text=True, timeout=3000)
H = {}
for line in r.stdout.splitlines():
    t = line.split()
    if t and t[0] == "COEF":
        H[t[1]] = [int(c) % p for c in t[2:]]
assert len(H) == 17, r.stdout[-2000:] + r.stderr[-2000:]
m = nmod_poly(H["a_2_2"], p)
roots = [(-int(f[0]) * pow(int(f[1]), -1, p)) % p for f, e in m.factor()[1] if f.degree() == 1]
roots = [int(x) for x in roots]
print(f"p = {p}: deg m = {m.degree()}, F_p-rational roots: {len(roots)}")


def ev_poly(coeffs, x):
    return sum(c * pow(x, i, p) for i, c in enumerate(coeffs)) % p


points = []
for th in roots:
    pt = {v: ev_poly(H[v], th) for v in H if v != "a_2_2"}
    pt["a_2_2"] = th
    pt.update(norm)
    for k in eqs:                                    # independent re-check of block -4
        if w(k) == -4:
            s = sum(c * pt[pv] * pt[qv] for c, pv, qv in eqs[k]) - (pt["lam"] if k == tgt else 0)
            assert s % p == 0
    points.append(pt)
print("all rational E5 points verified against the weight -4 equations (pure Python)")

os.makedirs("msolve_runs", exist_ok=True)
nfail = 0
for ip, pt in enumerate(points):
    polys = []
    for k in sorted(eqs):
        if w(k) < -3:
            continue
        terms = {}
        for c, pv, qv in eqs[k]:
            coef = c
            mon = []
            for v in (pv, qv):
                if v in pt and v not in rest:
                    coef = coef * pt[v] % p
                else:
                    mon.append(v)
            coef %= p
            if coef:
                kk = "*".join(sorted(mon))
                terms[kk] = (terms.get(kk, 0) + coef) % p
        polys.append("+".join(f"{c}*{mm}" for mm, c in terms.items() if c) or "0")
    assert all(pp != "0" for pp in polys)
    ok_u = 0
    for u in rest:
        fn = f"msolve_runs/p{p}_pt{ip}_{u}.ms"
        with open(fn, "w") as f:
            f.write(",".join(rest) + "\n" + f"{p}\n" + ",\n".join(polys + [f"{u}-1"]) + "\n")
        rr = subprocess.run(["msolve", "-f", fn, "-o", fn + ".out"], capture_output=True, text=True, timeout=3000)
        res = open(fn + ".out").read().strip()
        if res.startswith("[-1]"):
            ok_u += 1
        else:
            nfail += 1
            print("FAIL: point", ip, "variable", u, "msolve output:", res[:200])
    print(f"point {ip} (a_2_2 = {pt['a_2_2']}): {ok_u}/{len(rest)} variables forced to 0")
print("NFAIL", nfail)
print("OVERALL:", "PASS" if nfail == 0 and len(points) == 5 else "FAIL/INCOMPLETE", "p =", p, "points =", len(points))
