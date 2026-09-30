# Independent check of logs/k5_minor_certificate.json (own K5 arithmetic; no flint, no author code).
import json, sys, time
from fractions import Fraction as F
import sympy as sp
c = json.load(open(sys.argv[1]))
Rc = [F(x) for x in c["field_defining_polynomial"]]           # low -> high: 26,0,3,3,-1,1
assert Rc == [26,0,3,3,-1,1], Rc
w = sp.symbols('w'); Rpoly = sp.Poly([int(x) for x in reversed(Rc)], w)
print("R =", Rpoly.as_expr(), "| factor_list over Q:", sp.factor_list(Rpoly.as_expr()), "| disc =", sp.discriminant(Rpoly.as_expr(), w))
def mulw(v):            # multiply K5 element (5 coeffs) by w, reduce with w^5 = -(26 + 0w + 3w^2 + 3w^3 - w^4)
    top = v[4]; out = [F(0)] + v[:4]
    return [out[i] - top*Rc[i] for i in range(5)]
def multmat(e):         # 5x5 rational matrix of x -> e*x in basis 1,w,..,w^4 (columns = e*w^k)
    cols=[]; v=list(e)
    for k in range(5):
        cols.append(v); v=mulw(v)
    return [[cols[k][i] for k in range(5)] for i in range(5)]
def rank_Q(A):
    A=[row[:] for row in A]; r=0; ncol=len(A[0])
    for col in range(ncol):
        piv=next((i for i in range(r,len(A)) if A[i][col]!=0),None)
        if piv is None: continue
        A[r],A[piv]=A[piv],A[r]; p=A[r][col]
        for i in range(r+1,len(A)):
            if A[i][col]!=0:
                f=A[i][col]/p; A[i]=[a-f*b for a,b in zip(A[i],A[r])]
        r+=1
    return r
M=[[ [F(x) for x in e] for e in row] for row in c["matrix_35x6"]]
assert len(M)==35 and all(len(r)==6 for r in M)
maxdig=max(len(str(abs(x.numerator)))+len(str(x.denominator)) for row in M for e in row for x in e)
print("entries: max digits (num+den) =", maxdig)
t=time.time()
B=[]
for row in M:
    blocks=[multmat(e) for e in row]
    for i in range(5): B.append([blocks[j][i][k] for j in range(6) for k in range(5)])
rq=rank_Q(B); print(f"restriction of scalars: 175x30 rational matrix, rank_Q = {rq} -> rank over K5 = {rq/5} ({time.time()-t:.1f}s)")
# determinant of the pivot 6x6 over K5, via rank of its 30x30 restriction (nonzero det <=> full rank 30)
P=[M[i] for i in c["pivot_rows"]]
Bp=[]
for row in P:
    blocks=[multmat(e) for e in row]
    for i in range(5): Bp.append([blocks[j][i][k] for j in range(6) for k in range(5)])
print("pivot rows", c["pivot_rows"], "-> 30x30 restriction rank =", rank_Q(Bp))
# exact K5 determinant by Leibniz-free elimination with own inverse (solve e*x = 1 via 5x5 system)
def kmul(a,b):
    prod=[F(0)]*9
    for i in range(5):
        for j in range(5): prod[i+j]+=a[i]*b[j]
    for d in range(8,4,-1):           # reduce w^d, d>=5: w^5 = -(26 + 3w^2 + 3w^3 - w^4)
        t_=prod[d]; prod[d]=F(0)
        if t_!=0:
            for i in range(5): prod[d-5+i]-=t_*Rc[i]
    return prod[:5]
def kinv(a):
    A=multmat(a); b=[F(1),F(0),F(0),F(0),F(0)]
    n=5; Aug=[A[i][:]+[b[i]] for i in range(n)]
    for col in range(n):
        piv=next(i for i in range(col,n) if Aug[i][col]!=0); Aug[col],Aug[piv]=Aug[piv],Aug[col]
        p=Aug[col][col]; Aug[col]=[x/p for x in Aug[col]]
        for i in range(n):
            if i!=col and Aug[i][col]!=0:
                f=Aug[i][col]; Aug[i]=[x-f*y for x,y in zip(Aug[i],Aug[col])]
    return [Aug[i][n] for i in range(n)]
A=[[e[:] for e in row] for row in P]; det=[F(1),F(0),F(0),F(0),F(0)]; sign=1
for col in range(6):
    piv=next(i for i in range(col,6) if any(x!=0 for x in A[i][col]))
    if piv!=col: A[col],A[piv]=A[piv],A[col]; sign=-sign
    det=kmul(det,A[col][col]); iv=kinv(A[col][col])
    for i in range(col+1,6):
        if any(x!=0 for x in A[i][col]):
            f=kmul(A[i][col],iv); A[i]=[[x-y for x,y in zip(A[i][k],kmul(f,A[col][k]))] for k in range(6)]
if sign<0: det=[-x for x in det]
stored=[F(x) for x in c["minor_6x6_determinant"]]
print("own K5 determinant == stored determinant:", det==stored, "| nonzero:", any(x!=0 for x in det))
