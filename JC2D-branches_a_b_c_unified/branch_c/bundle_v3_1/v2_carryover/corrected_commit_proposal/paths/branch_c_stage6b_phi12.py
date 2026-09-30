#!/usr/bin/env python3
"""
branch_c_stage6b_phi12.py — Stage 6b: compute Phi_1, Phi_2 correctly.

Fix: E_0 (18x17 rank 17) — select 17 independent rows, solve the 17x17
system for (A_{-3}, B_{-2}) as formal polynomials (valid modulo Psi).
Then build RHS_{E_{-1}} and Phi_i = Z_i . RHS_{E_{-1}}.

Run with: ~/miniconda3/envs/physics/bin/python branch_c_stage6b_phi12.py
"""

import json, sys
from flint import fmpq_poly, fmpq
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

def solve_square(M, rhs):
    """Solve Mx=rhs for square invertible M (list of lists), return x or None."""
    n=len(M); aug=[M[i][:]+[rhs[i]] for i in range(n)]
    for c in range(n):
        piv=next((i for i in range(c,n) if aug[i][c]!=ZERO),None)
        if piv is None: return None
        aug[c],aug[piv]=aug[piv],aug[c]; iv=kinv(aug[c][c])
        aug[c]=[(x*iv)%Rr for x in aug[c]]
        for i in range(n):
            if i!=c and aug[i][c]!=ZERO:
                f=aug[i][c]; aug[i]=[(aug[i][j]-f*aug[c][j])%Rr for j in range(n+1)]
    return [aug[i][n] for i in range(n)]

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

print("="*70); print("STAGE 6b: Phi_1, Phi_2 (corrected)"); print("="*70)

# ---- Reconstruct (t,s,r,q) solution (abbreviated: reuse Stage 6 logic)
# For brevity, we rebuild quickly using the same steps as stage6.
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

A2c={i:pt.get(f"a_{i}_{2*i-2}",ZERO) for i in range(1,9)}
B3c={i:pt.get(f"b_{i}_{2*i-3}",ZERO) for i in range(2,13)}
def dderiv(p): return {e-1:(c*e)%Rr for e,c in p.items() if e>0}
B3d=dderiv(B3c); A2d=dderiv(A2c)

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
def vexp(v): return int(v.split('_')[1])
def ass4(vars):
    P={}
    for v in vars:
        e=vexp(v); P[e]=ts4_add(P.get(e,{}),aval[v])
        if not P[e]: del P[e]
    return P

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
kOp,_,_=nullspace(Op,NC)
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
            dd[v]=ts4_add(dd.get(v,{}),{m+(0,0):sol[j]})
for j,v in enumerate(E2v):
    dd=b0_ad if j<12 else am1_ad
    if kOp[0][j]!=ZERO: dd[v]=ts4_add(dd.get(v,{}),{(0,0,0,0,1,0):kOp[0][j]})
    if kOp[1][j]!=ZERO: dd[v]=ts4_add(dd.get(v,{}),{(0,0,0,0,0,1):kOp[1][j]})

# 7-var helpers
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
k1,_,_=nullspace(M1,NC1)
aval6={v:{k+(0,0):c for k,c in p.items()} for v,p in aval.items()}
def lift6(ad): return {v:{k+(0,):c for k,c in p.items()} for v,p in ad.items()}
a7base={}; a7base.update(lift6(aval6)); a7base.update(lift6(b0_ad)); a7base.update(lift6(am1_ad))
A0x=ass7([v for v in A0B1 if v[0]=='a'],a7base); B1x=ass7([v for v in A0B1 if v[0]=='b'],a7base)
A1x=ass7([v for v in A1B2 if v[0]=='a'],a7base); B2x=ass7([v for v in A1B2 if v[0]=='b'],a7base)
B0x=ass7(B0v,a7base); Am1x=ass7(Am1v,a7base)
RHS1=up7_add(up7_add(up7_mul(up7_deriv(A0x),B1x),up7_scale(up7_mul(A1x,up7_deriv(B0x)),-1)),
            up7_add(up7_mul(Am1x,up7_deriv(B2x)),up7_scale(up7_mul(up7_deriv(Am1x),B2x),2)))
monos1=sorted({k for p in RHS1.values() for k in p.keys()})
Am2v=[f"a_{i}_{2*i-1}" for i in range(0,7)]; Bm1v=[f"b_{i}_{2*i-1}" for i in range(0,12)]
E1v=Am2v+Bm1v
am2_ad={}; bm1_ad={}
for m in monos1:
    rhs=[RHS1[e].get(m,ZERO) if e in RHS1 else ZERO for e in ue1]
    sol=solve_aug(M1,rhs)
    if sol is None: continue
    for j,v in enumerate(E1v):
        if sol[j]!=ZERO:
            dd=am2_ad if j<7 else bm1_ad
            dd[v]=ts7_add(dd.get(v,{}),{m+(0,):sol[j]})
for j,v in enumerate(E1v):
    dd=am2_ad if j<7 else bm1_ad
    if k1[0][j]!=ZERO: dd[v]=ts7_add(dd.get(v,{}),{(0,0,0,0,0,0,1):k1[0][j]})

# ---- E_0: find 17 independent rows, solve 17x17
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
# Find 17 independent rows via greedy
ind_rows=[]; 
for i in range(len(M0)):
    test=[M0[j] for j in ind_rows+[i]]
    # rank via quick check
    Mt=[r[:] for r in test]; rr=0
    for c in range(NC0):
        piv=next((ii for ii in range(rr,len(Mt)) if Mt[ii][c]!=ZERO),None)
        if piv is None: continue
        Mt[rr],Mt[piv]=Mt[piv],Mt[rr]; iv=kinv(Mt[rr][c]); Mt[rr]=[(x*iv)%Rr for x in Mt[rr]]
        for ii in range(len(Mt)):
            if ii!=rr and Mt[ii][c]!=ZERO:
                f=Mt[ii][c]; Mt[ii]=[(Mt[ii][j]-f*Mt[rr][j])%Rr for j in range(NC0)]
        rr+=1
    if rr==len(ind_rows)+1:
        ind_rows.append(i)
    if len(ind_rows)==17: break
print(f"E_0: selected {len(ind_rows)} independent rows (dropped u-exp {ue0[[i for i in range(len(M0)) if i not in ind_rows][0]]})")
M0s=[M0[i] for i in ind_rows]; ue0s=[ue0[i] for i in ind_rows]

a7full=dict(a7base); a7full.update(am2_ad); a7full.update(bm1_ad)
Am2x=ass7(Am2v,a7full); Bm1x=ass7(Bm1v,a7full)
RHS0=up7_add(up7_add(up7_scale(up7_add(up7_mul(Am2x,up7_deriv(B2x)),up7_mul(up7_deriv(Am2x),B2x)),2),
                    up7_add(up7_mul(Am1x,up7_deriv(B1x)),up7_mul(up7_deriv(Am1x),B1x))),
            up7_scale(up7_add(up7_mul(A1x,up7_deriv(Bm1x)),up7_mul(up7_deriv(A1x),Bm1x)),-1))
monos0=sorted({k for p in RHS0.values() for k in p.keys()})
Am3v=[f"a_{i}_{2*i-3}" for i in range(0,6)]; Bm2v=[f"b_{i}_{2*i-2}" for i in range(0,11)]
E0v=Am3v+Bm2v
am3_ad={}; bm2_ad={}
for m in monos0:
    rhs=[RHS0[e].get(m,ZERO) if e in RHS0 else ZERO for e in ue0s]
    sol=solve_square(M0s,rhs)
    assert sol is not None, f"17x17 solve failed for {m}"
    for j,v in enumerate(E0v):
        if sol[j]!=ZERO:
            dd=am3_ad if j<6 else bm2_ad
            dd[v]=ts7_add(dd.get(v,{}),{m:sol[j]})
print(f"E_0 formal solution: A_{{-3}} ({len(am3_ad)} vars), B_{{-2}} ({len(bm2_ad)} vars)")

# ---- RHS_{E_{-1}} and Phi
a7e0=dict(a7full); a7e0.update(am3_ad); a7e0.update(bm2_ad)
Am3x=ass7(Am3v,a7e0); Bm2x=ass7(Bm2v,a7e0)
RHSm1=up7_add(
    up7_add(up7_scale(up7_mul(Am3x,up7_deriv(B2x)),3),
            up7_scale(up7_mul(up7_deriv(Am3x),B2x),2)),
    up7_add(
        up7_add(up7_scale(up7_mul(Am2x,up7_deriv(B1x)),2),
                up7_mul(up7_deriv(Am2x),B1x)),
        up7_add(up7_mul(Am1x,up7_deriv(B0x)),
            up7_add(up7_scale(up7_mul(up7_deriv(A0x),Bm1x),-1),
                up7_add(up7_scale(up7_mul(A1x,up7_deriv(Bm2x)),-1),
                        up7_scale(up7_mul(up7_deriv(A1x),Bm2x),-2))))))
Em1d={}; NCm1=15
for i in range(0,5):
    col={}
    for e,c in B3d.items(): col[e+i]=(col.get(e+i,ZERO)-4*c)%Rr
    if i>0:
        for e,c in B3c.items(): col[e+i-1]=(col.get(e+i-1,ZERO)-3*i*c)%Rr
    for ue,v in col.items(): Em1d.setdefault(ue,[ZERO]*NCm1)[i]=v
for j in range(0,10):
    col={}
    if j>0:
        for e,c in A2c.items(): col[e+j-1]=(col.get(e+j-1,ZERO)+2*j*c)%Rr
    for e,c in A2d.items(): col[e+j]=(col.get(e+j,ZERO)+3*c)%Rr
    for ue,v in col.items(): Em1d.setdefault(ue,[ZERO]*NCm1)[5+j]=v
uem1=sorted(Em1d.keys()); Mm1=[Em1d[e] for e in uem1]
MTm1=[[Mm1[r][c] for r in range(len(Mm1))] for c in range(NCm1)]
kTm1,_,_=nullspace(MTm1,len(Mm1))
print(f"E_{{-1}} left nullspace dim {len(kTm1)}")
Phi=[]
for zi in kTm1:
    Ph={}
    for idx,e in enumerate(uem1):
        wv=zi[idx]
        if wv==ZERO or e not in RHSm1: continue
        for k,v in RHSm1[e].items(): Ph[k]=(Ph.get(k,ZERO)+wv*v)%Rr
    Ph={k:v for k,v in Ph.items() if v!=ZERO}
    Phi.append(Ph)
for i,Ph in enumerate(Phi):
    print(f"Phi_{i+1}: {len(Ph)} monomials")
    # show monomial exponents
    for k in sorted(Ph)[:10]: print(f"   {k}")
    if len(Ph)>10: print(f"   ... and {len(Ph)-10} more")

# Save Phi for ideal test
import pickle
with open(_os.path.join(WORKDIR, "stage6_phi.pkl"),"wb") as f:
    pickle.dump([[(k,[str(c) for c in v]) for k,v in Ph.items()] for Ph in Phi], f)
print("\nSTAGE 6b DONE")
