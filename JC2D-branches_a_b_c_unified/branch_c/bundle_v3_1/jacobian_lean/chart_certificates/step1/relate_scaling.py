"""Is pipeline(x) = c_n * lower_c(alpha * x) for a diagonal scaling alpha of the 7 parameters?  Test via ratios."""
import pickle, sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lowerc_chart import *
AUD = os.environ.get("AUDIT_DIR", os.path.join(HERE, "..", "..", "audit_repro"))
d = pickle.load(open(os.path.join(AUD, "audit_fix.pkl"), "rb"))
pipe = {n: {tuple(m): K(c) for m, c in P.items()} for n, P in d["polys"].items()}
pipe["Omega"] = {tuple(m): K(c) for m, c in d["Omega"].items()}
C7 = load7()
pairs = [("Omega", "Omega"), ("Psi", "Psi"), ("Phi1", "Phi1"), ("Phi2", "Phi2"), ("Th1", "Theta1"), ("Th2", "Theta2"), ("Th3", "Theta3")]
ratio = {}
for a, b in pairs:
    ratio[b] = {m: (pipe[a][m] * kinv(C7[b][m])) % Rr for m in C7[b]}
# Omega test: r(T2^2 S2)^2 == r(S2^2) r(T2^4) ?
r = ratio["Omega"]; r1, r2, r3 = r[(0,0,0,2,0,0,0)], r[(0,2,0,1,0,0,0)], r[(0,4,0,0,0,0,0)]
print("Omega ratios consistent with a diagonal scaling (r2^2 == r1 r3):", (r2 * r2 - r1 * r3) % Rr == 0)
# general test: for each generator, ratios r_m / r_m0 must be multiplicative in the exponent difference.
# pick pairs of monomials differing by the same exponent vector across different generators and compare.
def diff(m, n): return tuple(a - b for a, b in zip(m, n))
table = {}
bad = 0
for nm, rr in ratio.items():
    ms = list(rr)
    for m, n in itertools.combinations(ms, 2):
        dv = diff(m, n); q = (rr[m] * kinv(rr[n])) % Rr
        if dv in table:
            if (table[dv] - q) % Rr != 0: bad += 1
        else: table[dv] = q
print("exponent differences seen:", len(table), " inconsistencies with a single diagonal scaling:", bad)
# kappa comparison
Om = pipe["Omega"]; o1, o2 = Om[(0,0,0,2,0,0,0)], Om[(0,2,0,1,0,0,0)]
kp = (-o2 * kinv(2 * o1)) % Rr; kl = kappa(C7)
print("kappa_pipeline == kappa_lower_c:", kp == kl)
