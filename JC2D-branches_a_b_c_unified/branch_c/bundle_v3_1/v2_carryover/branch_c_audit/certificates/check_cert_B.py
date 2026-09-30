"""check_cert_B.py -- independent (FLINT, not Singular) check of the characteristic-0 certificate for patch B
(t1 = 0, t2 = 1, s2 = kappa; corrected E1 solve):  1 = sum_i L_i * F_i  in K5[s1,r1,r2,q], K5 = Q[w]/(R).
L_i: exported from Singular's lift (cert_B.txt).  F_i: rebuilt in Python from audit_fix.pkl exactly as
k5_patches.py does, and compared character-for-character with the ideal in work/K5_B_lift.sing."""
import pickle, sys, time
sys.set_int_max_str_digits(0)
from flint import fmpq_poly, fmpq
AUD = sys.argv[1]            # branch_c_audit directory
CERT = sys.argv[2]           # cert_B.txt
perturb = len(sys.argv) > 3  # negative control
Rr = fmpq_poly([26, 0, 3, 3, -1, 1])
Z = fmpq_poly([0])
K = lambda cs: fmpq_poly([fmpq(*map(int, c.split('/'))) if '/' in c else fmpq(int(c)) for c in cs]) % Rr
def kinv(a):
    g, s, _ = a.xgcd(Rr); assert g == 1; return s % Rr
d = pickle.load(open(f"{AUD}/audit_fix.pkl", "rb"))
Om = {k: K(v) for k, v in d["Omega"].items()}
c1, c2, c3 = Om[(0,0,0,2,0,0,0)], Om[(0,2,0,1,0,0,0)], Om[(0,4,0,0,0,0,0)]
kap = (-c2 * kinv(2 * c1)) % Rr
assert (c1 * kap * kap + c2 * kap + c3) % Rr == 0
F = []
for name, p in d["polys"].items():
    out = {}
    for m, c in p.items():
        a, b, cc, dd, e, f, g = m
        if a > 0: continue                       # t1 = 0
        key = (cc, e, f, g)                      # t2 = 1, s2 = kappa
        out[key] = (out.get(key, Z) + K(c) * kap ** dd) % Rr
    F.append({k: v for k, v in out.items() if v != 0})
# tie F to the Singular input: regenerate the ideal text with k5_patches' printer and compare
def k5str(a):
    terms = [f"({c})" + ("" if k == 0 else f"*w^{k}") for k, c in enumerate(list(a)) if c != 0]
    return "(" + "+".join(terms) + ")" if terms else "0"
vars_ = ["s1", "r1", "r2", "q"]
txt = ",".join("+".join(k5str(cv) + ("*" + "*".join(f"{x}^{e}" for x, e in zip(vars_, key) if e) if any(key) else "")
                        for key, cv in sorted(Fi.items())) for Fi in F)
line = next(l for l in open(f"{AUD}/work/K5_B_lift.sing") if l.startswith("ideal I="))
assert line.strip() == f"ideal I={txt};", "F does not match the Singular input"
print(f"F: {len(F)} generators, {sum(map(len, F))} terms; identical to the ideal in K5_B_lift.sing")
# the certificate
L = [dict() for _ in F]
for ln in open(CERT):
    if ln.startswith("#"): continue
    i, ex, co = ln.strip().split(";")
    e = tuple(int(x) for x in ex.split(","))
    num, _, den = co.partition("/")
    c = fmpq(int(num), int(den) if den else 1)
    Li = L[int(i) - 1]
    key = e[1:]
    Li[key] = Li.get(key, Z) + fmpq_poly([0] * e[0] + [c])
if perturb:
    k0 = next(iter(L[0])); L[0][k0] = L[0][k0] + fmpq_poly([fmpq(1, 10**6)])
print(f"L: {sum(map(len, L))} K5-terms; max coefficient size {max(len(str(c)) for Li in L for v in Li.values() for c in list(v))} digits")
t = time.time()
S = {}
for Li, Fi in zip(L, F):
    for ka, va in Li.items():
        for kb, vb in Fi.items():
            k = tuple(x + y for x, y in zip(ka, kb))
            S[k] = S.get(k, Z) + va * vb
S = {k: v % Rr for k, v in S.items()}
S = {k: v for k, v in S.items() if v != 0}
ok = (S == {(0, 0, 0, 0): fmpq_poly([1])})
print(f"sum_i L_i F_i reduced mod R: {len(S)} nonzero terms; equals 1: {ok}  ({time.time() - t:.1f}s)")
sys.exit(0 if ok else 1)
