"""Chart t2 = 1, s2 = kappa, with the pipeline's six conditions and/or the six pure-row conditions
it omitted (E1: u^19; E0: u^18; E-1: u^17, u^18; E-2: u^16, u^17).  mod 101 (w = 9) and exact K5."""
from audit_env import need_singular
SINGULAR = need_singular()
import pickle, subprocess, sys
from fractions import Fraction as F
from flint import fmpq_poly, fmpq
Rr=fmpq_poly([26,0,3,3,-1,1])
K=lambda cs: fmpq_poly([fmpq(*map(int,c.split('/'))) if '/' in c else fmpq(int(c)) for c in cs])%Rr
def kinv(a):
    g,s,_=a.xgcd(Rr); assert g==1; return s%Rr
d=pickle.load(open('audit_fix.pkl','rb')); dx=pickle.load(open('audit_extra_fix.pkl','rb'))
Om={k:K(v) for k,v in d['Omega'].items()}
kap=(-Om[(0,2,0,1,0,0,0)]*kinv(2*Om[(0,0,0,2,0,0,0)]))%Rr
polys={n:{k:K(v) for k,v in p.items()} for n,p in d['polys'].items()}
extra={n:{k:K(v) for k,v in p.items()} for n,p in dx.items()}
for n,p in extra.items():
    vs=sorted({i for k in p for i,e in enumerate(k) if e})
    print(n, len(p), "terms; variables", [['t1','t2','s1','s2','r1','r2','q'][i] for i in vs])
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
def conv(p):
    out={}
    for m,c in p.items():
        key,cv=sub(m,c); out[key]=(out.get(key,fmpq_poly([0]))+cv)%Rr
    tK=[]; tp=[]
    for key,cv in sorted(out.items()):
        if cv==0: continue
        mono="*".join(f"{x}^{e}" for x,e in zip(vars_,key) if e)
        tK.append(k5str(cv)+("*"+mono if mono else "")); v=red(cv)
        if v: tp.append(f"{v}"+("*"+mono if mono else ""))
    return ("+".join(tK) if tK else "0"), ("+".join(tp) if tp else "0")
allp={**polys, **extra}
conv_all={n:conv(p) for n,p in allp.items()}
print("X1_19 at s2=kappa*t2^2 vanishes identically (K5):", conv_all['X1_19'][0]=="0")
sets={"pipe6":list(polys), "extra5":[n for n in extra if n!='X1_19'], "all11":list(polys)+[n for n in extra if n!='X1_19']}
for name,names in sets.items():
    eqp=[conv_all[n][1] for n in names]
    s=(f"ring R=101,({','.join(vars_)}),dp;\nideal I={','.join(eqp)};\nideal G=slimgb(I);\n"
       f"print(\"size=\"+string(size(G))); print(G[1]); print(\"dim=\"+string(dim(G)));\n"
       "if (size(G)==1 && deg(G[1])==0) { matrix L=lift(I,ideal(1)); int n=0; int i; for(i=1;i<=nrows(L);i++){n=n+size(L[i,1]);} print(\"lift terms=\"+string(n)); }\n")
    open(f"work/T2x_{name}_101.sing","w").write(s)
    r=subprocess.run([SINGULAR,"-q",f"work/T2x_{name}_101.sing"],capture_output=True,text=True,timeout=600,stdin=subprocess.DEVNULL)
    print(name, "mod 101:", " | ".join(l for l in r.stdout.split("\n") if l.strip())[:200])
    eqK=[conv_all[n][0] for n in names]
    sK=(f"ring R=(0,w),({','.join(vars_)}),dp;\nminpoly=w^5-w^4+3*w^3+3*w^2+26;\n"
        f"ideal I={','.join(eqK)};\nint t=timer; ideal G=slimgb(I);\nprint(\"size(G)=\"+string(size(G))); print(G[1]); print(\"secs=\"+string(timer-t));\n")
    open(f"work/K5_T2x_{name}.sing","w").write(sK)
