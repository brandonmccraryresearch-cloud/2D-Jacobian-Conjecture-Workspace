#!/usr/bin/env python3
"""
branch_c_stage4_e0_descent.py — Branch (c) Stage 4.

Part 1: Evaluate Omega(t,s,r) = V_1 . RHS_{E_1}(t,s,r).
  - Solve E_2 for (B_0, A_{-1}) = particular(t,s) + r_1*e_1 + r_2*e_2.
  - RHS_{E_1} = A_0'*B_1 - A_1*B_0' + (A_{-1}*B_2' + 2*A_{-1}'*B_2).
  - Contract with V_1 (E_1 left nullvector). Zero or not?

Part 2: E_0 operator (M=-1, y^1).
  - A_{-3}: u^0..u^5 (6). B_{-2}: u^0..u^10 (11).
  - O = -(3*A_{-3}*B_3' + 3*A_{-3}'*B_3) + (2*A_2*B_{-2}' + 2*A_2'*B_{-2}).
  - Dimensions, exact rank/K_5, mod-101, nullspaces.

Run with: ~/miniconda3/envs/physics/bin/python branch_c_stage4_e0_descent.py
"""

import json, sys
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
    """Solve M x = rhs (M m×n). Returns particular x or None."""
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

print("="*70); print("PART 1: OMEGA(t,s,r) = V_1 . RHS_{E_1}"); print("="*70)

# ---- E_4 kernel
M4=jacobian(-3,A1B2); k4,_,_=nullspace(M4,len(A1B2)); assert len(k4)==2
tval={u:{(1,0):k4[0][i],(0,1):k4[1][i]} for i,u in enumerate(A1B2)}

# ---- E_3: K(t), particular, kernel
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
M3=jacobian(-2,A0B1); k3,piv3,rref3=nullspace(M3,len(A0B1)); assert len(k3)==2
part={}
for tm in [(2,0),(1,1),(0,2)]:
    rhs=[(-q.get(tm,ZERO))%Rr for q in Kt]
    sol=solve_aug(M3,rhs); assert sol is not None
    for j,u in enumerate(A0B1):
        if sol[j]!=ZERO: part.setdefault(u,{})[tm]=sol[j]

# aval: variable -> {(e1,e2,e3,e4): coeff}  (t1,t2,s1,s2)
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

# ---- E_2 operator, solve for (B_0, A_{-1}) = part(t,s) + r-ker
A2c={i:pt.get(f"a_{i}_{2*i-2}",ZERO) for i in range(1,9)}
B3c={i:pt.get(f"b_{i}_{2*i-3}",ZERO) for i in range(2,13)}
def dderiv(p): return {e-1:(c*e)%Rr for e,c in p.items() if e>0}
B3d=dderiv(B3c)
NR,NB,NA=19,12,8; NC=NB+NA
Op=[[ZERO]*NC for _ in range(NR)]
for j in range(1,13):
    for e,c in A2c.items():
        ue=e+j-1
        if 1<=ue<=19: Op[ue-1][j-1]=(Op[ue-1][j-1]+2*j*c)%Rr
for i in range(0,8):
    for e,c in B3d.items():
        ue=e+i
        if 1<=ue<=19: Op[ue-1][NB+i]=(Op[ue-1][NB+i]-c)%Rr
    if i>0:
        for e,c in B3c.items():
            ue=e+i-1
            if 1<=ue<=19: Op[ue-1][NB+i]=(Op[ue-1][NB+i]-3*i*c)%Rr
kOp,_,_=nullspace(Op,NC); assert len(kOp)==2
print(f"E_2 operator: {NR}x{NC}, kernel dim {len(kOp)} (r-directions)")

# (t,s)-poly helpers (now 6 vars: t1,t2,s1,s2,r1,r2)
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
def assemble6(vars, ad):
    P={}
    for v in vars:
        e=vexp(v); P[e]=ts_add(P.get(e,{}),ad[v])
        if not P[e]: del P[e]
    return P

# Build RHS_{E_2}(t,s) as u-poly (4 vars), then solve E_2 per monomial
A0=assemble6([v for v in A0B1 if v[0]=='a'],aval)
B2=assemble6([v for v in A1B2 if v[0]=='b'],aval)
A1=assemble6([v for v in A1B2 if v[0]=='a'],aval)
B1=assemble6([v for v in A0B1 if v[0]=='b'],aval)
RHS2=up_add(up_scale(up_mul(up_deriv(A0),B2),2),
            up_add(up_scale(up_mul(A1,up_deriv(B1)),-1),up_mul(up_deriv(A1),B1)))
# Collect all (t,s)-monomials appearing
monos=set()
for p in RHS2.values(): monos.update(p.keys())
monos=sorted(monos)
print(f"RHS_{{E_2}}: {len(monos)} (t,s)-monomials, u-exps {sorted(RHS2.keys())}")

# Solve Op x = rhs_m for each monomial m -> particular; lift to 6 vars
B0_vars=[f"b_{i}_{2*i}" for i in range(1,13)]  # B_0: b_{i,2i}, i=1..12
Am1_vars=[f"a_{i}_{2*i+1}" for i in range(0,8)]  # A_{-1}: a_{i,2i+1}, i=0..7
E2_vars=B0_vars+Am1_vars
b0_ad={}; am1_ad={}  # var -> 6-var poly
for m in monos:
    rhs=[RHS2[e].get(m,ZERO) if e in RHS2 else ZERO for e in range(1,20)]
    sol=solve_aug(Op,rhs); assert sol is not None, f"E_2 unsolvable for {m}!"
    for j,v in enumerate(E2_vars):
        if sol[j]!=ZERO:
            key6=m+(0,0)
            dd=b0_ad if j<NB else am1_ad
            vv=v if j<NB else E2_vars[j]
            dd[vv]=ts_add(dd.get(vv,{}),{key6:sol[j]})
# Add r-kernel: r1*kOp[0] + r2*kOp[1]
for j,v in enumerate(E2_vars):
    if kOp[0][j]!=ZERO:
        dd=b0_ad if j<NB else am1_ad
        dd[v]=ts_add(dd.get(v,{}),{(0,0,0,0,1,0):kOp[0][j]})
    if kOp[1][j]!=ZERO:
        dd=b0_ad if j<NB else am1_ad
        dd[v]=ts_add(dd.get(v,{}),{(0,0,0,0,0,1):kOp[1][j]})
print(f"B_0, A_{{-1}}: particular + r-kernel assembled")

# Lift aval to 6 vars (pad with (0,0))
aval6={v:{k+(0,0):c for k,c in p.items()} for v,p in aval.items()}
B0=assemble6(B0_vars,b0_ad); Am1=assemble6(Am1_vars,am1_ad)
A0x=assemble6([v for v in A0B1 if v[0]=='a'],aval6)
B1x=assemble6([v for v in A0B1 if v[0]=='b'],aval6)
A1x=assemble6([v for v in A1B2 if v[0]=='a'],aval6)
B2x=assemble6([v for v in A1B2 if v[0]=='b'],aval6)

# RHS_{E_1} = A_0'*B_1 - A_1*B_0' + (A_{-1}*B_2' + 2*A_{-1}'*B_2)
RHS1=up_add(up_add(up_mul(up_deriv(A0x),B1x),up_scale(up_mul(A1x,up_deriv(B0)),-1)),
            up_add(up_mul(Am1,up_deriv(B2x)),up_scale(up_mul(up_deriv(Am1),B2x),2)))
print(f"RHS_{{E_1}}: u-exps {sorted(RHS1.keys())}")

# ---- E_1 operator + left nullvector V_1
A2d=dderiv(A2c)
E1d={}
NC1=7+12
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
MT1=[[M1[r][c] for r in range(len(M1))] for c in range(NC1)]
kT1,_,_=nullspace(MT1,len(M1)); assert len(kT1)==1
V1=kT1[0]
print(f"V_1: nonzero on u-exps {[ue1[i] for i,w in enumerate(V1) if w!=ZERO]}")

# Omega = sum_e V1[e] * RHS1[e]
Om={}
for idx,e in enumerate(ue1):
    wv=V1[idx]
    if wv==ZERO or e not in RHS1: continue
    for k,v in RHS1[e].items(): Om[k]=(Om.get(k,ZERO)+wv*v)%Rr
Om={k:v for k,v in Om.items() if v!=ZERO}
print(f"\nOmega(t,s,r): {len(Om)} monomials")
if Om:
    print("Monomial structure (t1,t2,s1,s2,r1,r2):")
    for k in sorted(Om): print(f"  {k}")
else:
    print("OMEGA IS IDENTICALLY ZERO.")

print("\n"+"="*70); print("PART 2: THE E_0 OPERATOR"); print("="*70)
# A_{-3}: u^0..u^5 (6); B_{-2}: u^0..u^10 (11)
# O = -(3*A_{-3}*B_3' + 3*A_{-3}'*B_3) + (2*A_2*B_{-2}' + 2*A_2'*B_{-2})
E0d={}
NC0=6+11
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
print(f"E_0: u-exps {ue0[0]}..{ue0[-1]} ({len(ue0)} eqs) x {NC0} unknowns")
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
rk0=rank_of(M0)
print(f"Rank over K_5 (exact): {rk0}")
print(f"Left nullity: {len(M0)-rk0}; kernel dim: {NC0-rk0}")
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
print(f"Rank mod 101: {rank101([[m101(x) for x in row] for row in M0])}")
print("\n"+"="*70); print("STAGE 4 SUMMARY"); print("="*70)
print(f"Omega monomials: {len(Om)}; E_0: {len(M0)}x{NC0}, rank {rk0}")
