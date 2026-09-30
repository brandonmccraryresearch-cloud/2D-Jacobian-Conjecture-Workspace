"""Independent (pure Python) check of the mod-101 certificate for the chart t2 = 1, s2 = kappa (w = 9):
1 = sum_i L_i F_i in F_101[t1,s1,r1,r2,q].  F_i rebuilt from audit_fix.pkl as chart_t2.py does and compared
with the ideal in work/T2_101.sing; L_i exported from Singular's lift."""
import pickle, sys
from fractions import Fraction as F
from flint import fmpq_poly, fmpq
sys.set_int_max_str_digits(0)
AUD, CERT = sys.argv[1], sys.argv[2]; perturb = len(sys.argv) > 3
P, W = 101, 9
Rr = fmpq_poly([26, 0, 3, 3, -1, 1])
K = lambda cs: fmpq_poly([fmpq(*map(int, c.split('/'))) if '/' in c else fmpq(int(c)) for c in cs]) % Rr
def kinv(a):
    g, s, _ = a.xgcd(Rr); assert g == 1; return s % Rr
def red(a):
    t = 0
    for k, c in enumerate(list(a)):
        f = F(str(c)); t = (t + f.numerator % P * pow(f.denominator % P, P - 2, P) * pow(W, k, P)) % P
    return t
d = pickle.load(open(f"{AUD}/audit_fix.pkl", "rb"))
Om = {k: K(v) for k, v in d["Omega"].items()}
kap = (-Om[(0,2,0,1,0,0,0)] * kinv(2 * Om[(0,0,0,2,0,0,0)])) % Rr
Fs = []
for n, p in d["polys"].items():
    out = {}
    for m, c in p.items():
        a, b, cc, dd, e, f, g = m
        key = (a, cc, e, f, g)
        out[key] = (out.get(key, fmpq_poly([0])) + K(c) * kap ** dd) % Rr
    Fs.append({k: red(v) for k, v in sorted(out.items()) if v != 0 and red(v)})
vars_ = ["t1", "s1", "r1", "r2", "q"]
txt = ",".join("+".join(f"{v}" + ("*" + "*".join(f"{x}^{e}" for x, e in zip(vars_, k) if e) if any(k) else "")
                        for k, v in Fi.items()) for Fi in Fs)
line = next(l for l in open(f"{AUD}/work/T2_101.sing") if l.startswith("ideal I="))
assert line.strip() == f"ideal I={txt};", "F does not match the Singular input"
L = [dict() for _ in Fs]
for ln in open(CERT):
    if ln.startswith("#"): continue
    i, ex, co = ln.strip().split(";")
    L[int(i) - 1][tuple(int(x) for x in ex.split(","))] = int(co) % P
if perturb:
    k0 = next(iter(L[0])); L[0][k0] = (L[0][k0] + 1) % P
S = {}
for Li, Fi in zip(L, Fs):
    for ka, va in Li.items():
        for kb, vb in Fi.items():
            k = tuple(x + y for x, y in zip(ka, kb)); S[k] = (S.get(k, 0) + va * vb) % P
S = {k: v for k, v in S.items() if v}
ok = S == {(0, 0, 0, 0, 0): 1}
print(f"F: {len(Fs)} generators, {sum(map(len, Fs))} terms (== T2_101.sing); L: {sum(map(len, L))} terms; "
      f"sum L_i F_i mod 101 has {len(S)} nonzero terms; equals 1: {ok}")
sys.exit(0 if ok else 1)
