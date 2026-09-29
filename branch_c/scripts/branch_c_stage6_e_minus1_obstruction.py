#!/usr/bin/env python3
"""
branch_c_stage6_e_minus1_obstruction.py — Branch (c) Stage 6.

1. Solve E_0 for unique (A_{-3}, B_{-2}) in 7 params (t1,t2,s1,s2,r1,r2,q).
2. Build RHS_{E_{-1}}, extract Z_1, Z_2, compute Phi_1, Phi_2.
3. E_{-2} operator: 16x13, rank/K_5, left nullity.
4. Attempt joint ideal test <Omega, Psi, Phi_1, Phi_2>.

Run with: ~/miniconda3/envs/physics/bin/python branch_c_stage6_e_minus1_obstruction.py
"""

import json, sys, os
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

key=lambda v:(v[0],int(v.split('_')[1]),int(v.split('_')[2]))
allv=sorted({v for T in eqs.values() for c,pv,qv in T for v in (pv,qv)},key=key)
A1B2=[v for v in allv if (v[0]=='a' and vw(v)==-1) or (v[0]=='b' and vw(v)==-2)]
A0B1=[v for v in allv if (v[0]=='a' and vw(v)==0 and v!='a_0_0') or (v[0]=='b' and vw(v)==-1)]

print("="*70); print("STAGE 6: E_{-1} OBSTRUCTION AND E_{-2}"); print("="*70)

# ---- (t,s) from E_4, E_3 (4-var)
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

# ---- E_2 -> (B_0, A_{-1}) in 6-var
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
kOp,_,_=nullspace(Op,NC)

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

# ---- E_1 -> (A_{-2}, B_{-1}) in 7-var
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
# E1 compatibility (fix): M1 has a one-dimensional left null space.  A right-hand side outside col(M1)
# has W.rhs equal to its coefficient in the E1 obstruction; the old `continue` dropped such monomials
# entirely, so the particular solution did not solve E1 even where the obstruction vanishes.  Project
# along e_j0 instead: where the obstruction vanishes, the projected right-hand sides add up to the true one.
_MTE1=[[M1[r][c] for r in range(len(M1))] for c in range(len(M1[0]))]
_NE1=nullspace(_MTE1,len(M1))[0]; assert len(_NE1)==1, 'left null space of M1 is not 1-dimensional'
_WE1=_NE1[0]
_jE1=next(j for j in range(len(_WE1)) if _WE1[j]!=ZERO)
def _proj_E1(rhs):
    wr=ZERO
    for j in range(len(_WE1)): wr=(wr+_WE1[j]*rhs[j])%Rr
    return [(rhs[j]-(wr*kinv(_WE1[_jE1]) if j==_jE1 else ZERO))%Rr for j in range(len(rhs))]
for m in monos1:
    rhs=[RHS1[e].get(m,ZERO) if e in RHS1 else ZERO for e in ue1]
    sol=solve_aug(M1,rhs)
    if sol is None: sol=solve_aug(M1,_proj_E1(rhs)); assert sol is not None  # Omega monomials: projected
    for j,v in enumerate(E1v):
        if sol[j]!=ZERO:
            dd=am2_ad if j<7 else bm1_ad
            dd[v]=ts7_add(dd.get(v,{}),{m+(0,):sol[j]})
for j,v in enumerate(E1v):
    dd=am2_ad if j<7 else bm1_ad
    if k1[0][j]!=ZERO: dd[v]=ts7_add(dd.get(v,{}),{(0,0,0,0,0,0,1):k1[0][j]})
print("E_1 solved (+q).")

# ---- E_0 -> (A_{-3}, B_{-2}) in 7-var (unique)
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

a7full=dict(a7base); a7full.update(am2_ad); a7full.update(bm1_ad)
Am2x=ass7(Am2v,a7full); Bm1x=ass7(Bm1v,a7full)
# RHS0 = 2*(A_{-2}*B_2' + A_{-2}'*B_2) + (A_{-1}*B_1' + A_{-1}'*B_1) - (A_1*B_{-1}' + A_1'*B_{-1})
RHS0=up7_add(up7_add(up7_scale(up7_add(up7_mul(Am2x,up7_deriv(B2x)),up7_mul(up7_deriv(Am2x),B2x)),2),
                    up7_add(up7_mul(Am1x,up7_deriv(B1x)),up7_mul(up7_deriv(Am1x),B1x))),
            up7_scale(up7_add(up7_mul(A1x,up7_deriv(Bm1x)),up7_mul(up7_deriv(A1x),Bm1x)),-1))
monos0=sorted({k for p in RHS0.values() for k in p.keys()})
Am3v=[f"a_{i}_{2*i-3}" for i in range(0,6)]; Bm2v=[f"b_{i}_{2*i-2}" for i in range(0,11)]
E0v=Am3v+Bm2v
am3_ad={}; bm2_ad={}
n_unsolv=0
# E0 compatibility (fix): M0 has a one-dimensional left null space.  A right-hand side outside col(M0)
# has W.rhs equal to its coefficient in the E0 obstruction; the old `continue` dropped such monomials
# entirely, so the particular solution did not solve E0 even where the obstruction vanishes.  Project
# along e_j0 instead: where the obstruction vanishes, the projected right-hand sides add up to the true one.
_MTE0=[[M0[r][c] for r in range(len(M0))] for c in range(len(M0[0]))]
_NE0=nullspace(_MTE0,len(M0))[0]; assert len(_NE0)==1, 'left null space of M0 is not 1-dimensional'
_WE0=_NE0[0]
_jE0=next(j for j in range(len(_WE0)) if _WE0[j]!=ZERO)
def _proj_E0(rhs):
    wr=ZERO
    for j in range(len(_WE0)): wr=(wr+_WE0[j]*rhs[j])%Rr
    return [(rhs[j]-(wr*kinv(_WE0[_jE0]) if j==_jE0 else ZERO))%Rr for j in range(len(rhs))]
for m in monos0:
    rhs=[RHS0[e].get(m,ZERO) if e in RHS0 else ZERO for e in ue0]
    sol=solve_aug(M0,rhs)
    if sol is None:
        n_unsolv+=1; sol=solve_aug(M0,_proj_E0(rhs)); assert sol is not None  # Psi monomials: projected
    for j,v in enumerate(E0v):
        if sol[j]!=ZERO:
            dd=am3_ad if j<6 else bm2_ad
            dd[v]=ts7_add(dd.get(v,{}),{m:sol[j]})
print(f"E_0 solved. Psi-carrying monomials projected (valid where Omega = Psi = 0): {n_unsolv} / {len(monos0)}")

# ---- RHS_{E_{-1}} and Phi_1, Phi_2
a7e0=dict(a7full); a7e0.update(am3_ad); a7e0.update(bm2_ad)
Am3x=ass7(Am3v,a7e0); Bm2x=ass7(Bm2v,a7e0)
# RHS = 3*A_{-3}*B_2' + 2*A_{-3}'*B_2 + 2*A_{-2}*B_1' + A_{-2}'*B_1
#       + A_{-1}*B_0' - A_0'*B_{-1} - A_1*B_{-2}' - 2*A_1'*B_{-2}
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
# E_{-1} operator and left nullvectors
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
print(f"E_{{-1}} left nullspace dim: {len(kTm1)}")
Z1,Z2=kTm1[0],kTm1[1]
Phi=[{},{}]
for zi,Ph in zip((Z1,Z2),Phi):
    for idx,e in enumerate(uem1):
        wv=zi[idx]
        if wv==ZERO or e not in RHSm1: continue
        for k,v in RHSm1[e].items(): Ph[k]=(Ph.get(k,ZERO)+wv*v)%Rr
    for k in list(Ph.keys()):
        if Ph[k]==ZERO: del Ph[k]
for i,Ph in enumerate(Phi):
    print(f"Phi_{i+1}: {len(Ph)} monomials")
    # print first few and check for t-free terms
    tfree=[k for k in Ph if k[0]==0 and k[1]==0]
    print(f"  t-free monomials: {len(tfree)}")

# ---- E_{-2} operator
print("\nE_{-2} OPERATOR:")
Em2d={}; NCm2=4+9
for i in range(0,4):  # A_{-5}: u^0..u^3
    col={}
    for e,c in B3d.items(): col[e+i]=(col.get(e+i,ZERO)-5*c)%Rr
    if i>0:
        for e,c in B3c.items(): col[e+i-1]=(col.get(e+i-1,ZERO)-3*i*c)%Rr
    for ue,v in col.items(): Em2d.setdefault(ue,[ZERO]*NCm2)[i]=v
for j in range(0,9):  # B_{-4}: u^0..u^8
    col={}
    if j>0:
        for e,c in A2c.items(): col[e+j-1]=(col.get(e+j-1,ZERO)+2*j*c)%Rr
    for e,c in A2d.items(): col[e+j]=(col.get(e+j,ZERO)+4*c)%Rr
    for ue,v in col.items(): Em2d.setdefault(ue,[ZERO]*NCm2)[4+j]=v
uem2=sorted(Em2d.keys()); Mm2=[Em2d[e] for e in uem2]
rk2=rank_of(Mm2)
print(f"  {len(Mm2)}x{NCm2} (u {uem2[0]}..{uem2[-1]}), rank {rk2}")
print(f"  left nullity {len(Mm2)-rk2}, kernel dim {NCm2-rk2}")
# mod 101
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
print(f"  rank mod 101: {rank101([[m101(x) for x in row] for row in Mm2])}")

print("\nSTAGE 6 CORE DONE")
