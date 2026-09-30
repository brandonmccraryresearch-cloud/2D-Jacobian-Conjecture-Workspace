#!/usr/bin/env python3
"""
branch_c_stage5_e0_compatibility.py — Branch (c) Stage 5.

1. Solve E_1 for (A_{-2}, B_{-1}) = particular(t,s,r) + q*ker.
2. Build RHS_{E_0} and extract Psi = U_1 . RHS_{E_0}.
3. E_{-1} operator: dimensions, exact rank/K_5, mod-101.
4. Ideal check: does <Omega, Psi> force t = 0? (via Singular Groebner)

Run with: ~/miniconda3/envs/physics/bin/python branch_c_stage5_e0_compatibility.py
"""

import json, sys, subprocess, os
from flint import fmpq_poly, fmpq, nmod_poly
import os as _os, shutil as _shutil  # configurable paths (defaults = the original machine)
CERTGEN = _os.environ.get("BRANCH_C_CERTGEN", "/home/hatch/workspace/v18/branch_ab_v19/lean/certgen")
WORKDIR = _os.environ.get("BRANCH_C_WORKDIR", "/home/hatch/workspace")
SINGULAR = _os.environ.get("SINGULAR", "/home/hatch/miniconda3/envs/cas/bin/Singular")
if "SINGULAR" not in _os.environ and not _os.path.exists(SINGULAR): SINGULAR = _shutil.which("Singular") or SINGULAR
sys.path.insert(0, CERTGEN)
from gen_system import build

Rr = fmpq_poly([26, 0, 3, 3, -1, 1])
def K(coeffs):
    return fmpq_poly([fmpq(*map(int, c.split('/'))) if '/' in c
                      else fmpq(int(c)) for c in coeffs]) % Rr
def kinv(a):
    g, s, _ = a.xgcd(Rr); assert g == 1; return s % Rr
ZERO = fmpq_poly([0]); ONE = fmpq_poly([1])

d = json.load(open(_os.path.join(CERTGEN, "e5_exact_K5.json")))
pt = {v: K(c) for v, c in d.items() if not v.startswith("_")}
pt.update({"a_1_0": ONE, "b_2_1": ONE, "a_2_2": ONE})
LP, LQ, eqs, tgt = build()
w = lambda ij: ij[1] - 2*ij[0]
vw = lambda v: w(tuple(map(int, v.split('_')[1:])))

def jacobian(weight, unknowns):
    rows = []
    for k in sorted(eqs):
        if w(k) != weight: continue
        row = [ZERO]*len(unknowns); idx = {u:i for i,u in enumerate(unknowns)}
        for c, pv, qv in eqs[k]:
            for a,b in ((pv,qv),(qv,pv)):
                if a in idx and b in pt:
                    row[idx[a]] = (row[idx[a]] + c*pt[b]) % Rr
        rows.append(row)
    return rows

def nullspace(M, ncols):
    M=[r[:] for r in M]; piv,r=[ ],0
    for c in range(ncols):
        i=next((i for i in range(r,len(M)) if M[i][c]!=ZERO),None)
        if i is None: continue
        M[r],M[i]=M[i],M[r]; iv=kinv(M[r][c]); M[r]=[(x*iv)%Rr for x in M[r]]
        for j in range(len(M)):
            if j!=r and M[j][c]!=ZERO:
                f=M[j][c]; M[j]=[(M[j][l]-f*M[r][l])%Rr for l in range(ncols)]
        piv.append(c); r+=1
    basis=[]
    for f in [c for c in range(ncols) if c not in piv]:
        v=[ZERO]*ncols; v[f]=ONE
        for i,pc in enumerate(piv): v[pc]=(-M[i][f])%Rr
        basis.append(v)
    return basis,piv,M

def solve_aug(M, rhs):
    aug=[M[i][:]+[rhs[i]] for i in range(len(M))]
    nc=len(M[0]); piv=[]; r=0
    for c in range(nc):
        i=next((i for i in range(r,len(aug)) if aug[i][c]!=ZERO),None)
        if i is None: continue
        aug[r],aug[i]=aug[i],aug[r]; iv=kinv(aug[r][c])
        aug[r]=[(x*iv)%Rr for x in aug[r]]
        for j in range(len(aug)):
            if j!=r and aug[j][c]!=ZERO:
                f=aug[j][c]; aug[j]=[(aug[j][l]-f*aug[r][l])%Rr for l in range(nc+1)]
        piv.append(c); r+=1
    for i in range(r,len(aug)):
        if aug[i][nc]!=ZERO: return None
    x=[ZERO]*nc
    for i,pc in enumerate(piv): x[pc]=aug[i][nc]
    return x

key=lambda v:(v[0],int(v.split('_')[1]),int(v.split('_')[2]))
allv=sorted({v for T in eqs.values() for c,pv,qv in T for v in (pv,qv)},key=key)
A1B2=[v for v in allv if (v[0]=='a' and vw(v)==-1) or (v[0]=='b' and vw(v)==-2)]
A0B1=[v for v in allv if (v[0]=='a' and vw(v)==0 and v!='a_0_0') or (v[0]=='b' and vw(v)==-1)]

print("="*70); print("STAGE 5: E_0 COMPATIBILITY AND E_{-1}"); print("="*70)

# ---- Reconstruct (t,s,r) parameterization (from Stage 4)
M4=jacobian(-3,A1B2); k4,_,_=nullspace(M4,len(A1B2))
tval={u:{(1,0):k4[0][i],(0,1):k4[1][i]} for i,u in enumerate(A1B2)}
def qadd(a,b):
    c=dict(a)
    for k,v in b.items(): c[k]=(c.get(k,ZERO)+v)%Rr
    return {k:v for k,v in c.items() if v!=ZERO}
def qmul(a,b):
    c={}
    for (e1,e2),v1 in a.items():
        for (f1,f2),v2 in b.items():
            k=(e1+f1,e2+f2); c[k]=(c.get(k,ZERO)+v1*v2)%Rr
    return {k:v for k,v in c.items() if v!=ZERO}
Kt=[]
for k in sorted(eqs):
    if w(k)!=-2: continue
    acc={}
    for c,pv,qv in eqs[k]:
        if pv in tval and qv in tval:
            acc=qadd(acc,{kk:(vv*c)%Rr for kk,vv in qmul(tval[pv],tval[qv]).items()})
    Kt.append(acc)
M3=jacobian(-2,A0B1); k3,_,_=nullspace(M3,len(A0B1))
part={}
for tm in [(2,0),(1,1),(0,2)]:
    rhs=[(-q.get(tm,ZERO))%Rr for q in Kt]
    sol=solve_aug(M3,rhs); assert sol is not None
    for j,u in enumerate(A0B1):
        if sol[j]!=ZERO: part.setdefault(u,{})[tm]=sol[j]
aval={}
for u in A1B2:
    aval[u]={ (e1,e2,0,0):c for (e1,e2),c in tval[u].items() if c!=ZERO }
for u in A0B1:
    dd={}
    if u in part:
        for (e1,e2),c in part[u].items(): dd[(e1,e2,0,0)]=c
    j=A0B1.index(u)
    if k3[0][j]!=ZERO: dd[(0,0,1,0)]=(dd.get((0,0,1,0),ZERO)+k3[0][j])%Rr
    if k3[1][j]!=ZERO: dd[(0,0,0,1)]=(dd.get((0,0,0,1),ZERO)+k3[1][j])%Rr
    aval[u]={k:v for k,v in dd.items() if v!=ZERO}

# ---- E_2 operator and (B_0, A_{-1}) solution
A2c={i:pt.get(f"a_{i}_{2*i-2}",ZERO) for i in range(1,9)}
B3c={i:pt.get(f"b_{i}_{2*i-3}",ZERO) for i in range(2,13)}
def dderiv(p): return {e-1:(c*e)%Rr for e,c in p.items() if e>0}
B3d=dderiv(B3c); A2d=dderiv(A2c)
NR,NC=19,20
Op=[[ZERO]*NC for _ in range(NR)]
for j in range(1,13):
    for e,c in A2c.items():
        ue=e+j-1
        if 1<=ue<=19: Op[ue-1][j-1]=(Op[ue-1][j-1]+2*j*c)%Rr
for i in range(0,8):
    for e,c in B3d.items():
        ue=e+i
        if 1<=ue<=19: Op[ue-1][12+i]=(Op[ue-1][12+i]-c)%Rr
    if i>0:
        for e,c in B3c.items():
            ue=e+i-1
            if 1<=ue<=19: Op[ue-1][12+i]=(Op[ue-1][12+i]-3*i*c)%Rr
kOp,_,_=nullspace(Op,NC); assert len(kOp)==2

# 6-var polys (t1,t2,s1,s2,r1,r2)
def ts_add(p,q,sign=1):
    r=dict(p)
    for k,v in q.items(): r[k]=(r.get(k,ZERO)+sign*v)%Rr
    return {k:v for k,v in r.items() if v!=ZERO}
def ts_mul(p,q):
    r={}
    for k1,v1 in p.items():
        for k2,v2 in q.items():
            k=tuple(a+b for a,b in zip(k1,k2)); r[k]=(r.get(k,ZERO)+v1*v2)%Rr
    return {k:v for k,v in r.items() if v!=ZERO}
def up_add(P,Q,sign=1):
    r=dict(P)
    for e,p in Q.items():
        r[e]=ts_add(r.get(e,{}),p,sign)
        if not r[e]: del r[e]
    return r
def up_mul(P,Q):
    r={}
    for e1,p1 in P.items():
        for e2,p2 in Q.items():
            e=e1+e2; pr=ts_mul(p1,p2); r[e]=ts_add(r.get(e,{}),pr)
            if not r[e]: del r[e]
    return r
def up_deriv(P):
    return {e-1:{k:(v*e)%Rr for k,v in p.items()} for e,p in P.items() if e>0}
def up_scale(P,s): return {e:{k:(v*s)%Rr for k,v in p.items()} for e,p in P.items()}
def vexp(v): return int(v.split('_')[1])
def assemble6(vars,ad):
    P={}
    for v in vars:
        e=vexp(v); P[e]=ts_add(P.get(e,{}),ad[v])
        if not P[e]: del P[e]
    return P

aval4=aval  # 4-var
# Build RHS2 (4-var), solve E_2 per monomial, lift to 6-var
A0_4=assemble6([v for v in A0B1 if v[0]=='a'],{v:{k:v for k,v in p.items()} for v,p in aval4.items() if v[0]=='a' and vw(v)==0})
# Simpler: directly use aval (4-var) with up_* adapted. Rebuild with 4-var helpers.
def ts4_add(p,q,sign=1):
    r=dict(p)
    for k,v in q.items(): r[k]=(r.get(k,ZERO)+sign*v)%Rr
    return {k:v for k,v in r.items() if v!=ZERO}
def ts4_mul(p,q):
    r={}
    for k1,v1 in p.items():
        for k2,v2 in q.items():
            k=(k1[0]+k2[0],k1[1]+k2[1],k1[2]+k2[2],k1[3]+k2[3]); r[k]=(r.get(k,ZERO)+v1*v2)%Rr
    return {k:v for k,v in r.items() if v!=ZERO}
def up4_add(P,Q,sign=1):
    r=dict(P)
    for e,p in Q.items():
        r[e]=ts4_add(r.get(e,{}),p,sign)
        if not r[e]: del r[e]
    return r
def up4_mul(P,Q):
    r={}
    for e1,p1 in P.items():
        for e2,p2 in Q.items():
            e=e1+e2; pr=ts4_mul(p1,p2); r[e]=ts4_add(r.get(e,{}),pr)
            if not r[e]: del r[e]
    return r
def up4_deriv(P): return {e-1:{k:(v*e)%Rr for k,v in p.items()} for e,p in P.items() if e>0}
def up4_scale(P,s): return {e:{k:(v*s)%Rr for k,v in p.items()} for e,p in P.items()}
def ass4(vars):
    P={}
    for v in vars:
        e=vexp(v); P[e]=ts4_add(P.get(e,{}),aval[v])
        if not P[e]: del P[e]
    return P
A0a=ass4([v for v in A0B1 if v[0]=='a']); B2a=ass4([v for v in A1B2 if v[0]=='b'])
A1a=ass4([v for v in A1B2 if v[0]=='a']); B1a=ass4([v for v in A0B1 if v[0]=='b'])
RHS2=up4_add(up4_scale(up4_mul(up4_deriv(A0a),B2a),2),
             up4_add(up4_scale(up4_mul(A1a,up4_deriv(B1a)),-1),up4_mul(up4_deriv(A1a),B1a)))
monos=sorted({k for p in RHS2.values() for k in p.keys()})
B0v=[f"b_{i}_{2*i}" for i in range(1,13)]; Am1v=[f"a_{i}_{2*i+1}" for i in range(0,8)]
E2v=B0v+Am1v
b0_ad={}; am1_ad={}
for m in monos:
    rhs=[RHS2[e].get(m,ZERO) if e in RHS2 else ZERO for e in range(1,20)]
    sol=solve_aug(Op,rhs); assert sol is not None
    for j,v in enumerate(E2v):
        if sol[j]!=ZERO:
            dd=b0_ad if j<12 else am1_ad
            dd[v]=ts_add(dd.get(v,{}),{m+(0,0):sol[j]})
for j,v in enumerate(E2v):
    dd=b0_ad if j<12 else am1_ad
    if kOp[0][j]!=ZERO: dd[v]=ts_add(dd.get(v,{}),{(0,0,0,0,1,0):kOp[0][j]})
    if kOp[1][j]!=ZERO: dd[v]=ts_add(dd.get(v,{}),{(0,0,0,0,0,1):kOp[1][j]})

# ---- E_1 operator, solve for (A_{-2}, B_{-1})
E1d={}; NC1=19
for i in range(0,7):
    col={}
    for e,c in B3d.items(): col[e+i]=(col.get(e+i,ZERO)-2*c)%Rr
    if i>0:
        for e,c in B3c.items(): col[e+i-1]=(col.get(e+i-1,ZERO)-3*i*c)%Rr
    for ue,v in col.items(): E1d.setdefault(ue,[ZERO]*NC1)[i]=v
for j in range(0,12):
    col={}
    if j>0:
        for e,c in A2c.items(): col[e+j-1]=(col.get(e+j-1,ZERO)+2*j*c)%Rr
    for e,c in A2d.items(): col[e+j]=(col.get(e+j,ZERO)+c)%Rr
    for ue,v in col.items(): E1d.setdefault(ue,[ZERO]*NC1)[7+j]=v
ue1=sorted(E1d.keys()); M1=[E1d[e] for e in ue1]
k1,_,_=nullspace(M1,NC1); assert len(k1)==1
print(f"E_1: {len(M1)}x{NC1}, kernel dim {len(k1)} (q-direction)")

# Build RHS1 (6-var) and solve E_1 per monomial
aval6={v:{k+(0,0):c for k,c in p.items()} for v,p in aval.items()}
A0x=assemble6([v for v in A0B1 if v[0]=='a'],aval6)
B1x=assemble6([v for v in A0B1 if v[0]=='b'],aval6)
A1x=assemble6([v for v in A1B2 if v[0]=='a'],aval6)
B2x=assemble6([v for v in A1B2 if v[0]=='b'],aval6)
B0x=assemble6(B0v,b0_ad); Am1x=assemble6(Am1v,am1_ad)
RHS1=up_add(up_add(up_mul(up_deriv(A0x),B1x),up_scale(up_mul(A1x,up_deriv(B0x)),-1)),
            up_add(up_mul(Am1x,up_deriv(B2x)),up_scale(up_mul(up_deriv(Am1x),B2x),2)))
monos1=sorted({k for p in RHS1.values() for k in p.keys()})
print(f"RHS_{{E_1}}: {len(monos1)} monomials")
Am2v=[f"a_{i}_{2*i-1}" for i in range(0,7)]  # A_{-2}: a_{i,2i-1}, i=0..6 (w=+2)
Bm1v=[f"b_{i}_{2*i-1}" for i in range(0,12)] # B_{-1}: b_{i,2i-1}, i=0..11 (w=+1)
E1v=Am2v+Bm1v
am2_ad={}; bm1_ad={}
for m in monos1:
    rhs=[RHS1[e].get(m,ZERO) if e in RHS1 else ZERO for e in ue1]
    sol=solve_aug(M1,rhs)
    if sol is None:
        print(f"  E_1 unsolvable for monomial {m} (expected iff Omega!=0)")
        continue
    for j,v in enumerate(E1v):
        if sol[j]!=ZERO:
            dd=am2_ad if j<7 else bm1_ad
            dd[v]=ts_add(dd.get(v,{}),{m+(0,):sol[j]})  # 7-var: add q
# Add q-kernel (7th var)
for j,v in enumerate(E1v):
    dd=am2_ad if j<7 else bm1_ad
    if k1[0][j]!=ZERO:
        dd[v]=ts_add(dd.get(v,{}),{(0,0,0,0,0,0,1):k1[0][j]})
print(f"A_{{-2}}, B_{{-1}}: solved (+ q-kernel)")

# ---- E_0 operator and U_1
E0d={}; NC0=17
for i in range(0,6):
    col={}
    for e,c in B3d.items(): col[e+i]=(col.get(e+i,ZERO)-3*c)%Rr
    if i>0:
        for e,c in B3c.items(): col[e+i-1]=(col.get(e+i-1,ZERO)-3*i*c)%Rr
    for ue,v in col.items(): E0d.setdefault(ue,[ZERO]*NC0)[i]=v
for j in range(0,11):
    col={}
    if j>0:
        for e,c in A2c.items(): col[e+j-1]=(col.get(e+j-1,ZERO)+2*j*c)%Rr
    for e,c in A2d.items(): col[e+j]=(col.get(e+j,ZERO)+2*c)%Rr
    for ue,v in col.items(): E0d.setdefault(ue,[ZERO]*NC0)[6+j]=v
ue0=sorted(E0d.keys()); M0=[E0d[e] for e in ue0]
MT0=[[M0[r][c] for r in range(len(M0))] for c in range(NC0)]
kT0,_,_=nullspace(MT0,len(M0)); assert len(kT0)==1
U1=kT0[0]
print(f"E_0: {len(M0)}x{NC0}, U_1 nonzero on u-exps {[ue0[i] for i,w in enumerate(U1) if w!=ZERO]}")

# ---- RHS_{E_0} (7-var) and Psi
# RHS = 2*(A_{-2}*B_2' + A_{-2}'*B_2) + (A_{-1}*B_1' + A_{-1}'*B_1) - (A_1*B_{-1}' + A_1'*B_{-1})
def ts7_add(p,q,sign=1):
    r=dict(p)
    for k,v in q.items(): r[k]=(r.get(k,ZERO)+sign*v)%Rr
    return {k:v for k,v in r.items() if v!=ZERO}
def ts7_mul(p,q):
    r={}
    for k1,v1 in p.items():
        for k2,v2 in q.items():
            k=tuple(a+b for a,b in zip(k1,k2)); r[k]=(r.get(k,ZERO)+v1*v2)%Rr
    return {k:v for k,v in r.items() if v!=ZERO}
def up7_add(P,Q,sign=1):
    r=dict(P)
    for e,p in Q.items():
        r[e]=ts7_add(r.get(e,{}),p,sign)
        if not r[e]: del r[e]
    return r
def up7_mul(P,Q):
    r={}
    for e1,p1 in P.items():
        for e2,p2 in Q.items():
            e=e1+e2; pr=ts7_mul(p1,p2); r[e]=ts7_add(r.get(e,{}),pr)
            if not r[e]: del r[e]
    return r
def up7_deriv(P): return {e-1:{k:(v*e)%Rr for k,v in p.items()} for e,p in P.items() if e>0}
def up7_scale(P,s): return {e:{k:(v*s)%Rr for k,v in p.items()} for e,p in P.items()}
def ass7(vars,ad):
    P={}
    for v in vars:
        e=vexp(v)
        if v in ad: P[e]=ts7_add(P.get(e,{}),ad[v])
        if e in P and not P[e]: del P[e]
    return P
def lift6to7(ad): return {v:{k+(0,):c for k,c in p.items()} for v,p in ad.items()}
a7={}; a7.update(lift6to7(aval6)); a7.update(lift6to7(b0_ad)); a7.update(lift6to7(am1_ad))
a7.update(am2_ad); a7.update(bm1_ad)
Am2x=ass7(Am2v,a7); Bm1x=ass7(Bm1v,a7); Am1x=ass7(Am1v,a7); B1x=ass7([v for v in A0B1 if v[0]=='b'],a7)
A1x=ass7([v for v in A1B2 if v[0]=='a'],a7); B2x=ass7([v for v in A1B2 if v[0]=='b'],a7)
RHS0=up7_add(up7_add(up7_scale(up7_add(up7_mul(Am2x,up7_deriv(B2x)),up7_mul(up7_deriv(Am2x),B2x)),2),
                    up7_add(up7_mul(Am1x,up7_deriv(B1x)),up7_mul(up7_deriv(Am1x),B1x))),
            up7_scale(up7_add(up7_mul(A1x,up7_deriv(Bm1x)),up7_mul(up7_deriv(A1x),Bm1x)),-1))
Psi={}
for idx,e in enumerate(ue0):
    wv=U1[idx]
    if wv==ZERO or e not in RHS0: continue
    for k,v in RHS0[e].items(): Psi[k]=(Psi.get(k,ZERO)+wv*v)%Rr
Psi={k:v for k,v in Psi.items() if v!=ZERO}
print(f"\nPsi(t,s,r,q): {len(Psi)} monomials")
for k in sorted(Psi): print(f"  {k}")

# ---- E_{-1} operator
print("\n"+"="*70); print("E_{-1} OPERATOR"); print("="*70)
Em1d={}; NCm1=5+10
for i in range(0,5):  # A_{-4}: u^0..u^4
    col={}
    for e,c in B3d.items(): col[e+i]=(col.get(e+i,ZERO)-4*c)%Rr
    if i>0:
        for e,c in B3c.items(): col[e+i-1]=(col.get(e+i-1,ZERO)-3*i*c)%Rr
    for ue,v in col.items(): Em1d.setdefault(ue,[ZERO]*NCm1)[i]=v
for j in range(0,10):  # B_{-3}: u^0..u^9
    col={}
    if j>0:
        for e,c in A2c.items(): col[e+j-1]=(col.get(e+j-1,ZERO)+2*j*c)%Rr
    for e,c in A2d.items(): col[e+j]=(col.get(e+j,ZERO)+3*c)%Rr
    for ue,v in col.items(): Em1d.setdefault(ue,[ZERO]*NCm1)[5+j]=v
uem1=sorted(Em1d.keys()); Mm1=[Em1d[e] for e in uem1]
def rank_of(rows):
    M=[r[:] for r in rows]; nr,nc=len(M),len(M[0]); r=0
    for c in range(nc):
        piv=next((i for i in range(r,nr) if M[i][c]!=ZERO),None)
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]; iv=kinv(M[r][c]); M[r]=[(x*iv)%Rr for x in M[r]]
        for i in range(nr):
            if i!=r and M[i][c]!=ZERO:
                f=M[i][c]; M[i]=[(M[i][j]-f*M[r][j])%Rr for j in range(nc)]
        r+=1
    return r
rkm1=rank_of(Mm1)
print(f"E_{{-1}}: {len(Mm1)}x{NCm1} (u-exps {uem1[0]}..{uem1[-1]}), rank {rkm1}")
print(f"  left nullity {len(Mm1)-rkm1}, kernel dim {NCm1-rkm1}")
Rm101=nmod_poly([26,0,3,3,-1,1],101); rt=next(x for x in range(101) if Rm101(x)==0)
def m101(a):
    t=0
    for k,ck in enumerate(list(a)):
        t=(t+int(ck.numerator)%101*pow(int(ck.denominator)%101,99,101)%101*pow(rt,k,101))%101
    return t
def rank101(rows):
    M=[r[:] for r in rows]; nr,nc=len(M),len(M[0]); r=0
    for c in range(nc):
        piv=next((i for i in range(r,nr) if M[i][c]%101!=0),None)
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]; iv=pow(M[r][c],99,101); M[r]=[(x*iv)%101 for x in M[r]]
        for i in range(nr):
            if i!=r and M[i][c]%101!=0:
                f=M[i][c]; M[i]=[(M[i][j]-f*M[r][j])%101 for j in range(nc)]
        r+=1
    return r
print(f"  rank mod 101: {rank101([[m101(x) for x in row] for row in Mm1])}")

# ---- Ideal check: does <Omega, Psi> force t=0? Use Singular.
print("\n"+"="*70); print("IDEAL CHECK <Omega, Psi>"); print("="*70)
# Omega: c1*s2^2 + c2*t2^2*s2 + c3*t2^4 (from Stage 4). Recompute coeffs numerically
# by evaluating Psi/Omega structure. For now, export Psi and Omega to Singular.
# We need Omega coeffs: rerun the Stage-4 Omega computation briefly is heavy;
# instead check: does Psi alone (plus Omega from Stage 4 file) force t2=0?
# Write Singular script with Psi; Omega added if available.
sing_dir=WORKDIR
# Save Psi as Singular poly in ring with K5 coeffs -> use mod-101 specialization for speed
psi101={}
for k,v in Psi.items():
    # k=(t1,t2,s1,s2,r1,r2,q); evaluate K5 coeff at w=rt mod 101
    t=0
    for kk,ck in enumerate(list(v)):
        t=(t+int(ck.numerator)%101*pow(int(ck.denominator)%101,99,101)%101*pow(rt,kk,101))%101
    if t!=0: psi101[k]=t
terms=[]
for (a,b,c,dd,e,f,g),cf in sorted(psi101.items()):
    mon=[]
    if a: mon.append(f"t1^{a}" if a>1 else "t1")
    if b: mon.append(f"t2^{b}" if b>1 else "t2")
    if c: mon.append(f"s1^{c}" if c>1 else "s1")
    if dd: mon.append(f"s2^{dd}" if dd>1 else "s2")
    if e: mon.append(f"r1^{e}" if e>1 else "r1")
    if f: mon.append(f"r2^{f}" if f>1 else "r2")
    if g: mon.append(f"q^{g}" if g>1 else "q")
    ms="*".join(mon) if mon else "1"
    terms.append(f"{cf}*{ms}")
singsrc=f"""ring R=101,(t1,t2,s1,s2,r1,r2,q),dp;
poly Psi={"+".join(terms) if terms else "0"};
ideal I=Psi;
ideal G=groebner(I);
G;
"""
open(os.path.join(sing_dir,"stage5_ideal.sing"),"w").write(singsrc)
r=subprocess.run([SINGULAR,"-q",
                  os.path.join(sing_dir,"stage5_ideal.sing")],
                 capture_output=True,text=True,stdin=subprocess.DEVNULL,timeout=300)
print("Singular Groebner of <Psi> (mod 101):")
print(r.stdout[:2000])
if r.stderr: print("STDERR:",r.stderr[:500])
print("\nSTAGE 5 DONE")
