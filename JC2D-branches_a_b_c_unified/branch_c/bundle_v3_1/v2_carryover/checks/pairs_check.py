# Validate: weight-n component of [P,Q] equals y^{1-(n+1)} * sum_{k+l=n+1} LT_{k,l}(A_k,B_l)(u), n = 4..-3,
# for random P, Q supported in the branch-(c) polygons.
import sympy as sp, random
random.seed(1)
x,y,u=sp.symbols('x y u')
inNP=lambda i,j: i<=8 and 2*i<=j+2 and j<=i+8
inNQ=lambda i,j: i<=12 and i<=2*j and 2*i<=j+3 and j<=i+12
NP=[(i,j) for i in range(13) for j in range(25) if inNP(i,j)]; NQ=[(i,j) for i in range(13) for j in range(25) if inNQ(i,j)]
P=sum(random.randint(-5,5)*x**i*y**j for i,j in NP); Q=sum(random.randint(-5,5)*x**i*y**j for i,j in NQ)
J=sp.expand(sp.diff(P,x)*sp.diff(Q,y)-sp.diff(P,y)*sp.diff(Q,x))
def layer(F,k):  # A_k(u): coefficient of x^i y^(2i-k)
    Fp=sp.Poly(F,x,y); return sum(c*u**m[0] for m,c in zip(Fp.monoms(),Fp.coeffs()) if 2*m[0]-m[1]==k)
def wpart(F,n):
    Fp=sp.Poly(F,x,y); return sum(c*x**m[0]*y**m[1] for m,c in zip(Fp.monoms(),Fp.coeffs()) if 2*m[0]-m[1]==n)
LT=lambda a,b,A,B: a*A*sp.diff(B,u)-b*sp.diff(A,u)*B
ok=True
for n in range(4,-4,-1):
    pairs=[(k,n+1-k) for k in range(-8,3) if -12<=n+1-k<=3]
    S=sp.expand(sum(LT(k,l,layer(P,k),layer(Q,l)) for k,l in pairs))
    lhs=sp.expand(wpart(J,n)); rhs=sp.expand((S.subs(u,x*y**2))*y**(-n))
    good=sp.simplify(lhs-rhs)==0; ok&=good
    print(f"weight {n:>2}: pairs {pairs} -> match {good}")
# layer u-exponent ranges
for k in range(2,-6,-1): print("A",k, sorted({i for i,j in NP if 2*i-j==k}))
for l in range(3,-5,-1): print("B",l, sorted({i for i,j in NQ if 2*i-j==l}))
print("ALL MATCH:", ok)
