"""Independent reproduction of the reported mod-109 result, from lower_c's conditions (conds_c.json):
   is (R(w), Psi, Phi1, Phi2, Theta1..3) at T2 = 1, S2 = kappa(w) the unit ideal in F_109[T1,S1,R1,R2,Q,w]?"""
import json, sys, subprocess, io, contextlib
from fractions import Fraction as F
sys.path.insert(0, "padic")
with contextlib.redirect_stdout(io.StringIO()):
    from check_cert import exact_checks
d = json.load(open("certgen_c/conds_c.json"))
with contextlib.redirect_stdout(io.StringIO()):
    polys, kap = exact_checks(d)
p = 109
def wpoly(a):                          # K5 element -> Singular polynomial in w with F_p coefficients (asserts p-integrality)
    terms = []
    for k, c in enumerate(a.coeffs()):
        f = F(str(c))
        assert f.denominator % p, "not p-integral"
        v = f.numerator % p * pow(f.denominator, -1, p) % p
        if v: terms.append(f"{v}*w^{k}")
    return "(" + ("+".join(terms) if terms else "0") + ")"
kw = wpoly(kap)
names = ["Psi", "Phi1", "Phi2", "Theta1", "Theta2", "Theta3"]
vs = ["T1", "S1", "R1", "R2", "Q"]; idx = {0: "T1", 2: "S1", 4: "R1", 5: "R2", 6: "Q"}
eqs = []
for n in names:
    terms = []
    for e, c in polys[n].items():
        mono = [f"{idx[i]}^{k}" for i, k in enumerate(e) if k and i in idx]
        if e[3]: mono.append(f"{kw}^{e[3]}")          # S2 = kappa(w); T2 = 1
        terms.append(wpoly(c) + ("*" + "*".join(mono) if mono else ""))
    eqs.append("+".join(terms))
S = [f"ring r={p},({','.join(vs)},w),dp;", "option(redSB);", f"poly Rw=w^5-w^4+3*w^3+3*w^2+26;",
     f"ideal I=Rw,{','.join(eqs)};", "ideal G=std(I);", 'print("G = "+string(G));',
     # control: drop Theta3 -> must NOT be the unit ideal if Theta3 is needed; report dimension
     f"ideal I5=Rw,{','.join(eqs[:-1])};", 'ideal G5=std(I5); print("control (Theta3 dropped): G[1] = "+string(G5[1])+", dim "+string(dim(G5)));',
     "quit;"]
open("padic/repro109.sing", "w").write("\n".join(S))
r = subprocess.run(["Singular", "-q", "padic/repro109.sing"], capture_output=True, text=True, stdin=subprocess.DEVNULL, timeout=3000)
print("kappa p-integral at 109: yes;", "all coefficients p-integral at 109: yes")
print(r.stdout.strip()[-800:], r.stderr.strip()[-800:])
