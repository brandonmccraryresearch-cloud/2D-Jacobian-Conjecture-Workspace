# Generate the Lean certificate that Omega is an exact square over K5 (house style: w with R(w)=0).
import pickle
import sympy as sp
from fractions import Fraction as F
w=sp.symbols('w'); R=sp.Poly(w**5-w**4+3*w**3+3*w**2+26,w,domain='QQ')
d=pickle.load(open('audit_fix.pkl','rb'))
Om=d['Omega']
def P(cs): return sp.Poly(sum(sp.Rational(c)*w**k for k,c in enumerate(cs)),w,domain='QQ')
c1=P(Om[(0,0,0,2,0,0,0)]); c2=P(Om[(0,2,0,1,0,0,0)]); c3=P(Om[(0,4,0,0,0,0,0)])
# kappa = -c2/(2 c1) in K5: inverse of c1 mod R
s_,t_,g=sp.gcdex(c1,R)          # s_*c1 + t_*R = g
assert g==sp.Poly(1,w,domain='QQ')
kap=(-c2*s_*sp.Rational(1,2)).rem(R)
def quo_exact(e):
    q,r=e.div(R); assert r.is_zero, r; return q
h_disc=quo_exact(c2**2-4*c1*c3)
h_lin =quo_exact(c2+2*c1*kap)
h_quad=quo_exact(c3-c1*kap**2)
h_inv =quo_exact(s_.rem(R)*c1-1)
u=s_.rem(R)
def lean(p):
    cs=p.all_coeffs()[::-1]; terms=[]
    for k,c in enumerate(cs):
        c=sp.Rational(c)
        if c==0: continue
        num=f"(({c.p}) / {c.q} : L)" if c.q!=1 else f"({c.p} : L)"
        terms.append(num+("" if k==0 else (" * w" if k==1 else f" * w ^ {k}")))
    return "(" + " + ".join(terms) + ")" if terms else "(0 : L)"
# mod-101 reductions at w = 9
def at9(p): return sum(sp.Rational(c)*9**k for k,c in enumerate(p.all_coeffs()[::-1]))
red=lambda q: (q.p%101)*pow(q.q%101,99,101)%101
vals={n:at9(p) for n,p in (('c1',c1),('c2',c2),('c3',c3),('kappa',kap))}
print({n:red(v) for n,v in vals.items()})
out=open('OmegaSquare_data.lean','w')
out.write(f"""/-- `c₁(w)`, the coefficient of `s₂²` in `Ω` (exact, `K₅ = ℚ[w]/(R)`). -/
def c1 (w : L) : L := {lean(c1)}
/-- `c₂(w)`, the coefficient of `t₂² s₂`. -/
def c2 (w : L) : L := {lean(c2)}
/-- `c₃(w)`, the coefficient of `t₂⁴`. -/
def c3 (w : L) : L := {lean(c3)}
/-- `κ(w) = −c₂/(2c₁)` in `K₅`. -/
def kappa (w : L) : L := {lean(kap)}
/-- `c₁(w)⁻¹` in `K₅`. -/
def c1inv (w : L) : L := {lean(u)}

/-- Division certificates: each identity below equals `R(w)` times this cofactor. -/
def hDisc (w : L) : L := {lean(h_disc)}
def hLin (w : L) : L := {lean(h_lin)}
def hQuad (w : L) : L := {lean(h_quad)}
def hInv (w : L) : L := {lean(h_inv)}
""")
out.close()
import json
json.dump({n:(str(v.p),str(v.q)) for n,v in vals.items()}, open('omega_at9.json','w'))
print("degrees:", c1.degree(), c2.degree(), c3.degree(), kap.degree(), "| cofactor degrees:", h_disc.degree(), h_lin.degree(), h_quad.degree(), h_inv.degree())
print("digits of largest numerator in c's:", max(len(str(abs(sp.Rational(c).p))) for p in (c1,c2,c3) for c in p.all_coeffs()))
