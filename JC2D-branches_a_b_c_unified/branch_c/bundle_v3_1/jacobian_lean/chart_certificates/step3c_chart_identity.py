"""
step3c_chart_identity.py -- the chart generators used by step3b are the right polynomials, over K5 exactly.

lowerc_chart.chart(C7, kappa) collects coefficients (T2 -> 1, S2 -> kappa, per monomial).  This script uses a different
algorithm: it EVALUATES lower_c's conditions straight from certgen_c/conds_c.json at random integer points
(t1, s1, r1, r2, q), with T2 = 1 and S2 = kappa' (kappa' recomputed here from Omega's coefficients by its own inversion),
in exact K5 arithmetic (fmpq_poly mod R), and compares with the chart polynomials evaluated at the same points.
A nonzero difference of total degree <= 8 vanishes at a uniformly random point of {-10^6..10^6}^5 with probability
<= 8 / (2*10^6+1) (Schwartz-Zippel); N points drive this to (4e-6)^N.  Control: kappa' + 1 must disagree.
Also re-checks Omega = o1 (S2 - kappa T2^2)^2 exactly (all three coefficients) and o1 != 0.
"""
import sys, os, json, random, time
sys.set_int_max_str_digits(0)
sys.path.insert(0, os.path.join(os.path.abspath(os.path.dirname(__file__)), "step1"))
from flint import fmpq_poly, fmpq
from lowerc_chart import load7, kappa, chart, NAMES

R = fmpq_poly([26, 0, 3, 3, -1, 1])
CONDS = os.path.join(os.path.abspath(os.path.dirname(__file__)), "certgen_c", "conds_c.json")
lc = json.load(open(CONDS))
def K(cs):
    return fmpq_poly([fmpq(*map(int, s.split("/"))) if "/" in s else fmpq(int(s)) for s in cs]) % R
def inv(a):                                   # own inversion in K5: solve a*x = 1 by linear algebra over Q
    # matrix of multiplication by a on the basis 1, w, .., w^4
    cols = [((a * fmpq_poly([0] * k + [1])) % R) for k in range(5)]
    from flint import fmpq_mat
    M = fmpq_mat(5, 5, [cols[j][i] for i in range(5) for j in range(5)])
    x = M.solve(fmpq_mat(5, 1, [1, 0, 0, 0, 0]))
    return fmpq_poly([x[i, 0] for i in range(5)])

om = {tuple(sorted((v, e) for v, e in m)): K(cs) for m, cs in lc["Omega"]}
o1 = om[(("b_12_23", 2),)]; o2 = om[(("b_12_22", 2), ("b_12_23", 1))]; o3 = om[(("b_12_22", 4),)]
assert set(om) == {(("b_12_23", 2),), (("b_12_22", 2), ("b_12_23", 1)), (("b_12_22", 4),)}
assert o1 != 0
kap2 = (-o2 * inv(2 * o1)) % R
# Omega = o1 (S2 - kappa T2^2)^2  <=>  o2 = -2 o1 kappa  and  o3 = o1 kappa^2
sq_ok = ((o2 + 2 * o1 * kap2) % R == 0) and ((o3 - o1 * kap2 * kap2) % R == 0)
print("Omega = o1 (S2 - kappa T2^2)^2 exactly over K5, o1 != 0:", sq_ok)
C7 = load7(); kap = kappa(C7)
print("kappa (lowerc_chart) == kappa' (independent inversion):", kap == kap2)
ch = chart(C7, kap)

POS = {"b_11_20": 0, "b_11_21": 1, "a_6_13": 2, "a_7_15": 3, "b_10_21": 4}
def eval_direct(n, pt, kp):
    tot = fmpq_poly([0])
    for m, cs in lc[n]:
        v = K(cs)
        for var, e in m:
            if var == "b_12_22": continue                      # T2 = 1
            if var == "b_12_23": v = (v * kp ** e) % R
            else: v = v * pt[POS[var]] ** e
        tot = (tot + v) % R
    return tot
def eval_chart(n, pt):
    tot = fmpq_poly([0])
    for (t, s, r, u, q), c in ch[n].items():
        tot = (tot + c * (pt[0] ** t * pt[1] ** s * pt[2] ** r * pt[3] ** u * pt[4] ** q)) % R
    return tot
rnd = random.Random(20260929)
N = int(os.environ.get("NPTS", "12"))
t0 = time.time(); ok = True; ctl_differs = True
for k in range(N):
    pt = [rnd.randint(-10 ** 6, 10 ** 6) for _ in range(5)]
    for n in NAMES:
        ok &= (eval_direct(n, pt, kap2) == eval_chart(n, pt))
    if k < 2:                                                   # control: a wrong kappa must be detected
        ctl_differs &= any(eval_direct(n, pt, (kap2 + 1) % R) != eval_chart(n, pt) for n in NAMES)
print(f"chart generators == direct evaluation of conds_c.json at {N} random points (6 generators each): {ok}  "
      f"({time.time() - t0:.1f}s)")
print("control kappa' + 1 detected as different:", ctl_differs)
print("ALL:", "PASS" if (sq_ok and kap == kap2 and ok and ctl_differs) else "FAIL")
