"""
cert_fibers_singular.py  --  certificate step M (modular part), Singular implementation.

For a prime p:
 (M1) I5 = weight -4 block of [P,Q] = lam*x^2 with a_1_0 = b_2_1 = a_8_14 = 1, over F_p.
      Compute the lex GB (stdfglm) and ASSERT shape position w.r.t. a_2_2:
      one univariate element m(a_2_2) and, for every other variable v, an element v - h_v(a_2_2).
      Hence V_{F_p-bar}(I5 mod p) = { (h_v(th))_v : m(th) = 0 }.
 (M1b) Hensel input: the weight -4 block is a square system (17 equations, 17 unknowns: the 16
      weight -2/-3 coefficients and lam).  ASSERT det(Jacobian) is nonzero at every point of
      V(I5 mod p): gcd( NF(det J, G), m ) = 1.
 (M2) For every irreducible factor f of m over F_p (theta = a root; the other roots of f are
      Frobenius conjugates, and Frobenius maps fibre ideals to fibre ideals), work over
      F_p[theta]/(f) = F_{p^deg f} and form the fibre ideal
          J = < all equations of weight -3,-2,-1,0 > + < v - h_v(theta) : v in I5-variables >.
      ASSERT: for every weight>=-1 variable u there is N <= 40 with u^N in J (radical membership
      checked by reduce(u^N, std(J)) == 0).  Then V(J) = {0} in the weight>=-1 coordinates.
Prints PASS/FAIL lines; exits nonzero on any failure.
usage: python3 cert_fibers_singular.py p
"""
import subprocess, sys
from gen_system import build

p = int(sys.argv[1])
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
assert sorted(blocks) == [-4, -3, -2, -1, 0], sorted(blocks)
allvars = sorted({v for T in eqs.values() for c, pv, qv in T for v in (pv, qv)} - norm, key=key)
e5 = [v for v in allvars if (v[0] == 'a' and vw(v) == -2) or (v[0] == 'b' and vw(v) == -3)]
rest = [v for v in allvars if v not in e5]
# sanity: the weight -4 block involves exactly the e5 variables (+lam)
e5used = sorted({v for k in eqs if w(k) == -4 for c, pv, qv in eqs[k] for v in (pv, qv)} - norm, key=key)
assert e5used == e5, (e5used, e5)
assert len(rest) == 51 and len(e5) == 16, (len(rest), len(e5))
yw = lambda v: vw(v) + (2 if v[0] == 'a' else 3)
assert all(yw(v) == 0 for v in e5) and all(yw(v) >= 1 for v in rest)
for k in eqs:
    if w(k) >= -3:
        degs = {yw(pv) * (pv not in norm) + yw(qv) * (qv not in norm) for c, pv, qv in eqs[k]}
        assert degs == {w(k) + 4}, (k, degs)      # weighted homogeneous of degree W+4 >= 1
assert len(blocks[-4]) == 17                      # square system: 17 equations in 16 E5 vars + lam
lexvars = [v for v in e5 if v != "a_2_2"] + ["lam", "a_2_2"]
evars = rest + [v for v in e5 if v != "a_2_2"] + ["lam"]
restpolys = ",".join(blocks[-3] + blocks[-2] + blocks[-1] + blocks[0])
restcheck = "".join(
    f'N = 1; while (N <= 40 and reduce({u}^N, GJ) != 0) {{ N++; }} if (N > 40) {{ "FAIL radical {u}"; nfail++; }} else {{ if (N > maxN) {{ maxN = N; }} }}\n'
    for u in rest)

S = f"""
int nfail = 0;
ring L = {p}, ({','.join(lexvars)}), lp;
ideal I = {','.join(blocks[-4])};
ideal G = stdfglm(I);
// ---- (M1) shape-position assertions
int i, j, N, maxN, ok;
if (size(G) != nvars(L)) {{ "FAIL shape: size", size(G); nfail++; }}
ok = 1;
for (i = 1; i <= size(G); i++) {{
  if (i == 1) {{ if (leadmonom(G[1]) != a_2_2^deg(G[1])) {{ ok = 0; }} if (size(variables(G[1])) != 1) {{ ok = 0; }} }}
  else {{ if (leadmonom(G[i]) != var(nvars(L) - i + 1)) {{ ok = 0; }} if (deg(G[i] - leadcoef(G[i])*leadmonom(G[i]), intvec(0:(nvars(L)-1),1)) != deg(G[i] - leadcoef(G[i])*leadmonom(G[i]))) {{ ok = 0; }} }}
}}
if (ok) {{ "PASS shape position; deg m =", deg(G[1]); }} else {{ "FAIL shape position"; nfail++; }}
// ---- (M1b) Jacobian determinant nonzero at every point of V(I5 mod p)
poly dJ = reduce(det(jacob(I)), G);
if (deg(gcd(dJ, G[1])) != 0 or dJ == 0) {{ "FAIL Jacobian"; nfail++; }} else {{ "PASS Jacobian det nonzero at all", deg(G[1]), "points"; }}
list F = factorize(G[1]);
int totdeg = 0; string fs, hs; int fdeg, fmult;
for (i = 1; i <= size(F[1]); i++) {{
  if (deg(F[1][i]) > 0) {{
    totdeg = totdeg + deg(F[1][i]) * F[2][i];
    fs = string(F[1][i]); fdeg = deg(F[1][i]); fmult = F[2][i];
    hs = "";
    for (j = 1; j <= nvars(L) - 1; j++) {{ hs = hs + "," + string(var(j)) + "-(" + string(reduce(var(j), G)) + ")"; }}
    execute("ring E = (" + string({p}) + ", a_2_2), ({','.join(evars)}), dp;");
    execute("minpoly = " + fs + ";");
    execute("ideal J = {restpolys}" + hs + ";");
    int t0 = rtimer;
    ideal GJ = std(J);

    maxN = 0;
    {restcheck}
    "fibre over factor", i, "deg", fdeg, "mult", fmult, ": dim", dim(GJ), " vdim", vdim(GJ), " max N", maxN, " time", rtimer - t0;
    setring L;
    nfail = nfail + 0;
    kill E;
  }}
}}
"total degree of factors:", totdeg;
if (totdeg != deg(G[1])) {{ "FAIL factor degrees"; nfail++; }}
"NFAIL", nfail;
quit;
"""

if __name__ == "__main__":
    r = subprocess.run(["Singular", "-q", "--no-rc"], input=S, capture_output=True, text=True, timeout=20000)
    out = "\n".join(l for l in r.stdout.splitlines() if "redefining" not in l)
    print(out)
    if r.stderr.strip():
        print("STDERR:", r.stderr[-3000:])
    bad = any(l.strip().startswith("FAIL") for l in out.splitlines()) or ("NFAIL 0" not in out) or ("error" in out.lower()) or ("?" in out)
    print("OVERALL:", "FAIL" if bad else "PASS", "p =", p)
    sys.exit(1 if bad else 0)
