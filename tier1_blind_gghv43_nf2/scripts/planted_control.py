"""
planted_control.py -- controls for the fibre step (same equation generator, same Singular calls).

Control A (planted solution): take an F_p-rational point xi5 of I5 (weight -4 block, a_1_0 =
  b_2_1 = a_8_14 = 1), a random nonzero fibre vector eta* in F_p^51, and replace every weight
  -3..0 equation e by e - e(xi5, eta*).  The modified system has the planted solution.
  EXPECT: std(J') != <1>; eta* satisfies J' exactly; the cone test (u^N in J') FAILS.
Control B (known non-trivial fibre): drop the weight-0 block (homogeneous).  Earlier exploration
  showed a 1-dim fibre; EXPECT: the cone test FAILS (some u^N not in J for N <= 40).
Control C (the real system, same code): EXPECT cone test PASSES.
usage: python3 planted_control.py p seed
"""
import subprocess, sys, random, re
from gen_system import build

p = int(sys.argv[1]); seed = int(sys.argv[2])
rng = random.Random(seed)
LP, LQ, eqs, tgt = build()
w = lambda ij: ij[1] - 2 * ij[0]
vw = lambda v: w(tuple(map(int, v.split('_')[1:])))
key = lambda v: (v[0], int(v.split('_')[1]), int(v.split('_')[2]))
norm = {"a_1_0", "b_2_1", "a_8_14"}
tok = lambda v: "1" if v in norm else v
allvars = sorted({v for T in eqs.values() for c, pv, qv in T for v in (pv, qv)} - norm, key=key)
e5 = [v for v in allvars if (v[0] == 'a' and vw(v) == -2) or (v[0] == 'b' and vw(v) == -3)]
rest = [v for v in allvars if v not in e5]
lexvars = [v for v in e5 if v != "a_2_2"] + ["lam", "a_2_2"]


def eqstr(k, shift=0):
    s = "+".join(f"({c})*{tok(pv)}*{tok(qv)}" for c, pv, qv in eqs[k])
    if k == tgt:
        s += "-lam"
    if shift:
        s += f"-({shift})"
    return s


def run(S):
    r = subprocess.run(["Singular", "-q", "--no-rc"], input=S, capture_output=True, text=True, timeout=5000)
    return "\n".join(l for l in r.stdout.splitlines() if "redefining" not in l) + r.stderr


# --- step 1: an F_p-rational point of I5
S1 = f"""
ring L = {p}, ({','.join(lexvars)}), lp;
ideal I = {','.join(eqstr(k) for k in sorted(eqs) if w(k) == -4)};
ideal G = stdfglm(I);
list F = factorize(G[1]); int i, j;
for (i = 1; i <= size(F[1]); i++) {{ if (deg(F[1][i]) == 1) {{ break; }} }}
poly f = F[1][i];
number th = -number(subst(f, a_2_2, 0)) / leadcoef(f);
"TH", th;
for (j = 1; j <= nvars(L) - 1; j++) {{ "VAL", string(var(j)), number(subst(reduce(var(j), G), a_2_2, th)); }}
quit;
"""
out = run(S1)
vals = {}
for line in out.splitlines():
    t = line.split()
    if t and t[0] == "TH":
        vals["a_2_2"] = int(t[1]) % p
    if t and t[0] == "VAL":
        vals[t[1]] = int(t[2]) % p
assert len(vals) == 17, out[-2000:]
for v in norm:
    vals[v] = 1
# check the E5 point satisfies the weight -4 block (independent Python evaluation)
def ev(k, pt):
    s = sum(c * pt[pv] * pt[qv] for c, pv, qv in eqs[k])
    if k == tgt:
        s -= pt["lam"]
    return s % p
assert all(ev(k, vals) == 0 for k in eqs if w(k) == -4), "E5 point does not satisfy block -4"
eta = {u: rng.randrange(1, p) for u in rest}
pt = dict(vals); pt.update(eta)
shift = {k: ev(k, pt) for k in eqs if w(k) >= -3}
print("control A: E5 point verified in Python; nonzero shifts:", sum(1 for s in shift.values() if s), "of", len(shift))

pins = ",".join(f"{v}-({vals[v]})" for v in e5 + ["lam"])
cone = "".join(
    f'if (bad == 0) {{ N = 1; while (N <= 12 and reduce({u}^N, GJ) != 0) {{ N++; }} if (N > 12) {{ bad++; "first failing var: {u}"; }} }}\n' for u in rest)
subst_eta = "".join(f"J2 = subst(J2, {u}, {eta[u]});" for u in rest)


def fibre_script(eqlist, label):
    return f"""
ring E = {p}, ({','.join(rest + e5 + ['lam'])}), dp;
ideal J = {','.join(eqlist)}, {pins};
ideal GJ = std(J);
int N; int bad = 0;
{cone}
"{label}: std==<1>?", (size(GJ)==1 and GJ[1]==1), " dim", dim(GJ), " #vars failing cone test", bad;
ideal J2 = J;
{subst_eta}
{''.join(f"J2 = subst(J2, {v}, {vals[v]});" for v in e5 + ['lam'])}
"{label}: planted point residual is zero?", (size(J2) == 0);
quit;
"""


A = [eqstr(k, shift[k]) for k in sorted(eqs) if w(k) >= -3]
print(run(fibre_script(A, "control A (planted)")).strip())
B = [eqstr(k) for k in sorted(eqs) if -3 <= w(k) <= -1]
print(run(fibre_script(B, "control B (no weight-0 block)")).strip())
C = [eqstr(k) for k in sorted(eqs) if w(k) >= -3]
print(run(fibre_script(C, "control C (real system)")).strip())
