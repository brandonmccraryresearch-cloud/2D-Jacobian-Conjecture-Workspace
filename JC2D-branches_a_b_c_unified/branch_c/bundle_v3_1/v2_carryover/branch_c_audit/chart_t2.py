"""Chart t2 = 1 (s2 = kappa): the vertex (12,24) forces t2 != 0 (Edge19.lean), and the weighted
scaling (t,s,r,q) -> (sig t, sig^2 s, sig^3 r, sig^4 q) fixes the top layer, so t2 = 1 covers every
branch-(c) solution.  Emits the mod-101 check (w = 9, kappa = 38) and the exact K5 input."""
import pickle, subprocess, sys
from fractions import Fraction as F
from flint import fmpq_poly, fmpq
Rr=fmpq_poly([26,0,3,3,-1,1])
K=lambda cs: fmpq_poly([fmpq(*map(int,c.split('/'))) if '/' in c else fmpq(int(c)) for c in cs])%Rr
def kinv(a):
    g,s,_=a.xgcd(Rr); assert g==1; return s%Rr
d=pickle.load(open('audit_fix.pkl','rb'))
Om={k:K(v) for k,v in d['Omega'].items()}
c1=Om[(0,0,0,2,0,0,0)]; c2=Om[(0,2,0,1,0,0,0)]
kap=(-c2*kinv(2*c1))%Rr
polys={n:{k:K(v) for k,v in p.items()} for n,p in d['polys'].items()}
vars_=['t1','s1','r1','r2','q']
def sub(m,c):
    a,b,cc,dd,e,f,g=m; return (a,cc,e,f,g), (c*kap**dd)%Rr
def k5str(a):
    terms=[]
    for k,c in enumerate(list(a)):
        if c==0: continue
        terms.append(f"({c})"+("" if k==0 else f"*w^{k}"))
    return "("+"+".join(terms)+")" if terms else "0"
P=101; W=9
def red(a):
    t=0
    for k,c in enumerate(list(a)):
        f=F(str(c)); t=(t+f.numerator%P*pow(f.denominator%P,P-2,P)*pow(W,k,P))%P
    return t
eqK=[]; eqp=[]
for n,p in polys.items():
    out={}
    for m,c in p.items():
        key,cv=sub(m,c); out[key]=(out.get(key,fmpq_poly([0]))+cv)%Rr
    termsK=[]; termsp=[]
    for key,cv in sorted(out.items()):
        if cv==0: continue
        mono="*".join(f"{x}^{e}" for x,e in zip(vars_,key) if e)
        termsK.append(k5str(cv)+("*"+mono if mono else ""))
        v=red(cv)
        if v: termsp.append(f"{v}"+("*"+mono if mono else ""))
    eqK.append("+".join(termsK) if termsK else "0"); eqp.append("+".join(termsp) if termsp else "0")
sp=(f"ring R=101,({','.join(vars_)}),dp;\nideal I={','.join(eqp)};\nint t=timer; ideal G=slimgb(I);\n"
    f"print(\"size(G)=\"+string(size(G))); print(G[1]); print(\"secs=\"+string(timer-t));\n"
    "matrix L=lift(I,ideal(1)); int n=0; int i; for(i=1;i<=nrows(L);i++){n=n+size(L[i,1]);} print(\"lift terms=\"+string(n));\n")
open("work/T2_101.sing","w").write(sp)
sK=(f"ring R=(0,w),({','.join(vars_)}),dp;\nminpoly=w^5-w^4+3*w^3+3*w^2+26;\n"
    f"ideal I={','.join(eqK)};\nint t=timer; ideal G=slimgb(I);\nprint(\"size(G)=\"+string(size(G))); print(G[1]); print(\"secs=\"+string(timer-t));\n")
open("work/K5_T2_fix.sing","w").write(sK)
print("equations:",len(eqK)," K5 bytes:",len(sK), " mod-101 bytes:", len(sp))
