"""Modular certificates for lower_c's chart ideal (T2 = 1, S2 = kappa; variables T1, S1, R1, R2, Q):
   (a) at a root r of R mod p:            1 = sum_i L_i F_i            in F_p[T1,S1,R1,R2,Q]
   (b) at the inert prime 109, w a variable: 1 = L_R R(w) + sum_i L_i F_i  in F_109[T1,S1,R1,R2,Q,w]
Singular (lift) only PRODUCES the cofactors; check_modp_chart.py verifies them without Singular."""
import sys, os, json, subprocess
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from lowerc_chart import *
C7 = load7(); kap = kappa(C7); ch = chart(C7, kap)
X = ["T1", "S1", "R1", "R2", "Q"]
def red(a, p, r):
    t = 0
    for k, c in enumerate(a.coeffs()):
        f = Fr(str(c)); assert f.denominator % p, "not p-integral"
        t = (t + f.numerator * pow(f.denominator, -1, p) * pow(r, k, p)) % p
    return t
def wpoly(a, p):
    terms = []
    for k, c in enumerate(a.coeffs()):
        f = Fr(str(c)); assert f.denominator % p, "not p-integral"
        v = f.numerator * pow(f.denominator, -1, p) % p
        if v: terms.append(f"{v}*w^{k}")
    return "(" + ("+".join(terms) if terms else "0") + ")"
def mono(e): return "*".join(f"{v}^{k}" for v, k in zip(X, e) if k)
def gens_str(p, r=None):
    out = []
    for n in NAMES:
        ts = []
        for e, c in ch[n].items():
            coef = str(red(c, p, r)) if r is not None else wpoly(c, p)
            if coef in ("0", "(0)"): continue
            ts.append(coef + ("*" + mono(e) if any(e) else ""))
        out.append("+".join(ts) if ts else "0")
    return out
def run(p, r, out):
    if r is None:
        ring = f"ring R={p},({','.join(X)},w),dp;"; I = ["w^5-w^4+3*w^3+3*w^2+26"] + gens_str(p)
    else:
        ring = f"ring R={p},({','.join(X)}),dp;"; I = gens_str(p, r)
    S = [ring, f"ideal I={','.join(I)};", "matrix C=lift(I,ideal(1));", f'link l=":w {out}";',
         'string s="["; int i; for (i=1;i<=ncols(I);i++) { s=s+"\\""+string(C[i,1])+"\\""; if (i<ncols(I)) { s=s+","; } }',
         's=s+"]"; write(l,s); close(l); print("ok"); quit;']
    open(os.path.join(HERE, "lift.sing"), "w").write("\n".join(S))
    res = subprocess.run(["Singular", "-q", os.path.join(HERE, "lift.sing")], capture_output=True, text=True,
                         stdin=subprocess.DEVNULL, timeout=3000)
    print(p, r, res.stdout.strip()[-200:], res.stderr.strip()[-400:], flush=True)
if __name__ == "__main__":
    for p, r in [(101, 9), (1000003, 806739), (109, None)]:
        tag = f"p{p}_w{r}" if r is not None else f"p{p}_inert"
        run(p, r, os.path.join(HERE, f"chartcert_{tag}.json"))
