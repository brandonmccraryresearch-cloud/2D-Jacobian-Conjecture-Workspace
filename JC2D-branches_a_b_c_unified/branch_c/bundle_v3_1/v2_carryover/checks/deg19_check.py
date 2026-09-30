# Independent check of the Degree-19 Rigidity argument (branch (c), GGHV Prop 4.3(1)).
import sympy as sp
from fractions import Fraction
# 1. Lattice / layer ranges from the half-plane description of the polygons
inNP = lambda i,j: 0<=i<=8 and j>=0 and j>=2*i-2 and j<=i+8
inNQ = lambda i,j: 0<=i<=12 and 2*j>=i and j>=2*i-3 and j<=i+12
def hull_pts(V):
    n=len(V); pts=set()
    for i in range(0,30):
        for j in range(0,40):
            if all((V[(k+1)%n][0]-V[k][0])*(j-V[k][1])-(V[(k+1)%n][1]-V[k][1])*(i-V[k][0])>=0 for k in range(n)): pts.add((i,j))
    return pts
NP=hull_pts([(0,0),(1,0),(8,14),(8,16),(0,8)]); NQ=hull_pts([(0,0),(2,1),(12,21),(12,24),(0,12)])
assert NP=={(i,j) for i in range(30) for j in range(40) if inNP(i,j)} and NQ=={(i,j) for i in range(30) for j in range(40) if inNQ(i,j)}
print("lattice points:", len(NP), len(NQ), "(half-plane description = convex hull: True)")
lay=lambda S,k: sorted(i for (i,j) in S if 2*i-j==k)
for name,S,ks in (("P",NP,(2,1,0,-1)),("Q",NQ,(3,2,1,0))):
    for k in ks: print(f"  {name} layer {k:>2}: u-exponents {lay(S,k)}")
# 2. E2 (weight-1) equation with generic coefficients on exactly these supports
u=sp.symbols('u')
def gen(name,exps): 
    cs=sp.symbols(f'{name}_0:{max(exps)+1}'); return sum(cs[i]*u**i for i in exps), cs
A2,a2=gen('a2',lay(NP,2)); A1,a1=gen('a1',lay(NP,1)); A0,a0=gen('a0',lay(NP,0)); Am1,am1=gen('am1',lay(NP,-1))
B3,b3=gen('b3',lay(NQ,3)); B2,b2=gen('b2',lay(NQ,2)); B1,b1=gen('b1',lay(NQ,1)); B0,b0=gen('b0',lay(NQ,0))
LT=lambda a,b,A,B: a*A*sp.diff(B,u)-b*sp.diff(A,u)*B
E2=sp.expand(LT(2,0,A2,B0)+LT(1,1,A1,B1)+LT(0,2,A0,B2)+LT(-1,3,Am1,B3))
print("E2 degree in u:", sp.degree(E2,u))
c19=sp.expand(E2.coeff(u,19)); print("u^19 coefficient of E2:", c19)
c19_t0=sp.expand(c19.subs({s:0 for s in a1}).subs({s:0 for s in b2})); print("at t=0 (A1=0, B2=0):", c19_t0)
print("deg(A_-1 B_3' + 3 A_-1' B_3) =", sp.degree(sp.expand(Am1*sp.diff(B3,u)+3*sp.diff(Am1,u)*B3),u))
# 3. Sharpness control: allow deg A_-1 = 8 -> counterexample with b0_12 != 0
A2c=u**8; Am1c=u**8; B3c=u**12
B0c=sp.integrate(sp.expand((Am1c*sp.diff(B3c,u)+3*sp.diff(Am1c,u)*B3c)/(2*A2c)),u)
print("control (deg A_-1 = 8): B0 =", B0c, "| check 2A2B0' = A-1B3'+3A-1'B3:", sp.expand(2*A2c*sp.diff(B0c,u)-(Am1c*sp.diff(B3c,u)+3*sp.diff(Am1c,u)*B3c))==0)
