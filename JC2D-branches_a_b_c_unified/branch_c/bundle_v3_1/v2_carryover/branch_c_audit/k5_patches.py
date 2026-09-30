import pickle, sys
from flint import fmpq_poly, fmpq
Rr=fmpq_poly([26,0,3,3,-1,1])
K=lambda cs: fmpq_poly([fmpq(*map(int,c.split('/'))) if '/' in c else fmpq(int(c)) for c in cs])%Rr
def kinv(a):
    g,s,_=a.xgcd(Rr); assert g==1; return s%Rr
tag=sys.argv[1]
d=pickle.load(open(f'audit_{tag}.pkl','rb'))
Om={k:K(v) for k,v in d['Omega'].items()}
c1=Om[(0,0,0,2,0,0,0)]; c2=Om[(0,2,0,1,0,0,0)]; c3=Om[(0,4,0,0,0,0,0)]
kap=(-c2*kinv(2*c1))%Rr
assert (c1*kap*kap+c2*kap+c3)%Rr==0   # kappa is the (double) root, exactly
print("kappa in K5:", kap, file=sys.stderr)
# reduce kappa mod 101 at w=9 as a check
from fractions import Fraction as F
red=lambda a: sum(F(str(c)).numerator*pow(F(str(c)).denominator,99,101)*pow(9,k,101) for k,c in enumerate(list(a)))%101
print("kappa mod 101 =", red(kap), file=sys.stderr)
def k5str(a):
    cs=list(a); terms=[]
    for k,c in enumerate(cs):
        if c==0: continue
        terms.append(f"({c})" + ("" if k==0 else f"*w^{k}"))
    return "("+"+".join(terms)+")" if terms else "0"
polys={n:{k:K(v) for k,v in p.items()} for n,p in d['polys'].items()}
def build(sub, vars_):
    eqs=[]
    for n,p in polys.items():
        out={}
        for m,c in p.items():
            r=sub(m,c)
            if r is None: continue
            key,cv=r; out[key]=(out.get(key,fmpq_poly([0]))+cv)%Rr
        terms=[]
        for key,cv in sorted(out.items()):
            if cv==0: continue
            mono="*".join(f"{x}^{e}" for x,e in zip(vars_,key) if e)
            terms.append(k5str(cv)+("*"+mono if mono else ""))
        eqs.append("+".join(terms) if terms else "0")
    return eqs
def subA(m,c):  # t1=1, s2=kappa*t2^2
    a,b,cc,dd,e,f,g=m; return (b+2*dd,cc,e,f,g), (c*kap**dd)%Rr
def subB(m,c):  # t1=0, t2=1, s2=kappa
    a,b,cc,dd,e,f,g=m
    if a>0: return None
    return (cc,e,f,g), (c*kap**dd)%Rr
for name,sub,vars_,wts in (("A",subA,['t2','s1','r1','r2','q'],[1,2,3,3,4]),("B",subB,['s1','r1','r2','q'],[2,3,3,4])):
    eqs=build(sub,vars_)
    s=(f"ring R=(0,w),({','.join(vars_)}),wp({','.join(map(str,wts))});\nminpoly=w^5-w^4+3*w^3+3*w^2+26;\n"
       f"ideal I={','.join(eqs)};\nint t=timer; ideal G=slimgb(I);\nprint(\"size(G)=\"+string(size(G))); print(G[1]); print(\"secs=\"+string(timer-t));\n")
    open(f"work/K5_{name}_{tag}.sing","w").write(s)
    print(name, "equations:", len(eqs), "bytes:", len(s), file=sys.stderr)
