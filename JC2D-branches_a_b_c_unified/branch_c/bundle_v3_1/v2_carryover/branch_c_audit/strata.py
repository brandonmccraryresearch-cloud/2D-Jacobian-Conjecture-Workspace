from audit_env import need_singular
SINGULAR = need_singular()
import pickle, subprocess, sys
from fractions import Fraction as F
P=101; W=9
def red(coeffs):  # K5 element (list of rational strings, low->high) -> F_101 at w=9
    t=0
    for k,c in enumerate(coeffs):
        f=F(c); t=(t+f.numerator%P*pow(f.denominator%P,P-2,P)*pow(W,k,P))%P
    return t
def run(tag, polys, subst, varnames, weights):
    eqs=[]
    for name,poly in polys.items():
        out={}
        for mono,c in poly.items():
            v=red(c)
            if v==0: continue
            r=subst(mono,v)
            if r is None: continue
            key,cv=r; out[key]=(out.get(key,0)+cv)%P
        out={k:v for k,v in out.items() if v}
        terms=[f"{v}*"+"*".join(f"{x}^{e}" for x,e in zip(varnames,k) if e) if any(k) else f"{v}" for k,v in sorted(out.items())]
        eqs.append("+".join(terms) if terms else "0")
    sing=f"ring R={P},({','.join(varnames)}),wp({','.join(map(str,weights))});\nideal I={','.join(eqs)};\nideal G=slimgb(I);\nprint(size(G)); print(G[1]); print(dim(G)); print(vdim(G));\n"
    fn=f"work/{tag}.sing"; open(fn,'w').write(sing)
    r=subprocess.run([SINGULAR,"-q",fn],capture_output=True,text=True,timeout=600,stdin=subprocess.DEVNULL)
    return [l for l in r.stdout.split('\n') if l.strip()][:4], r.stderr[:200]
K=38
for fix in ('orig','fix'):
    d=pickle.load(open(f'audit_{fix}.pkl','rb')); polys=d['polys']
    # patch A: t1=1, s2=K*t2^2 -> vars (t2,s1,r1,r2,q)
    def subA(m,v):
        a,b,c,dd,e,f,g=m; return (b+2*dd,c,e,f,g), v*pow(K,dd,P)%P
    # patch B: t1=0, t2=1, s2=K -> vars (s1,r1,r2,q)
    def subB(m,v):
        a,b,c,dd,e,f,g=m
        if a>0: return None
        return (c,e,f,g), v*pow(K,dd,P)%P
    # stratum t=0 (t1=t2=0, s2=0 since Omega=c1*s2^2) -> vars (s1,r1,r2,q), weighted-homogeneous
    def subC(m,v):
        a,b,c,dd,e,f,g=m
        if a>0 or b>0 or dd>0: return None
        return (c,e,f,g), v
    print(f"== {fix}: patch t1=1 (s2=38 t2^2):", *run(f"A_{fix}",polys,subA,['t2','s1','r1','r2','q'],[1,2,3,3,4]))
    print(f"== {fix}: patch t1=0,t2=1 (s2=38):", *run(f"B_{fix}",polys,subB,['s1','r1','r2','q'],[2,3,3,4]))
    print(f"== {fix}: stratum t=0 (s2=0):     ", *run(f"C_{fix}",polys,subC,['s1','r1','r2','q'],[2,3,3,4]))
