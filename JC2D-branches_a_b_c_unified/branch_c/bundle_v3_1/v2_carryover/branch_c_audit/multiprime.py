from audit_env import need_singular
SINGULAR = need_singular()
import pickle, subprocess, sympy as sp
from fractions import Fraction as F
from flint import fmpq_poly, fmpq, nmod_poly
Rr=fmpq_poly([26,0,3,3,-1,1])
K=lambda cs: fmpq_poly([fmpq(*map(int,c.split('/'))) if '/' in c else fmpq(int(c)) for c in cs])%Rr
d=pickle.load(open('audit_fix.pkl','rb'))
Om={k:K(v) for k,v in d['Omega'].items()}
c1=Om[(0,0,0,2,0,0,0)]; c2=Om[(0,2,0,1,0,0,0)]
g,s_,_=c1.xgcd(Rr); kap=(-c2*s_*fmpq(1,2))%Rr
polys={n:{m:K(c) for m,c in p.items()} for n,p in d['polys'].items()}
def red(a,p,r):
    t=0
    for k,c in enumerate(list(a)):
        f=F(str(c))
        if f.denominator%p==0: return None
        t=(t+f.numerator%p*pow(f.denominator%p,p-2,p)*pow(r,k,p))%p
    return t
def gb(p,r,patch):
    k=red(kap,p,r)
    if k is None: return "bad prime (kappa)"
    eqs=[]
    for n,poly in polys.items():
        out={}
        for (a,b,c,dd,e,f,g),cv in poly.items():
            v=red(cv,p,r)
            if v is None: return "bad prime"
            if v==0: continue
            if patch=='A': key=(b+2*dd,c,e,f,g); v=v*pow(k,dd,p)%p
            else:
                if a>0: continue
                key=(0,c,e,f,g); v=v*pow(k,dd,p)%p
            out[key]=(out.get(key,0)+v)%p
        vs=['t2','s1','r1','r2','q']
        terms=[f"{v}"+"".join(f"*{x}^{ee}" for x,ee in zip(vs,key) if ee) for key,v in out.items() if v]
        eqs.append("+".join(terms) if terms else "0")
    sing=f"ring R={p},(t2,s1,r1,r2,q),dp;\nideal I={','.join(eqs)};\nideal G=slimgb(I);\nprint(G[1]);\n"
    open('work/mp.sing','w').write(sing)
    out=subprocess.run([SINGULAR,"-q","work/mp.sing"],capture_output=True,text=True,stdin=subprocess.DEVNULL,timeout=600).stdout.strip()
    return out.split('\n')[0]
res=[]
for p in sp.primerange(200,5000):
    roots=[r for r in range(p) if (r**5-r**4+3*r**3+3*r**2+26)%p==0]
    if not roots: continue
    r=roots[0]
    res.append((p,r,gb(p,r,'A'),gb(p,r,'B')))
    if len(res)>=12: break
for x in res: print(x)
