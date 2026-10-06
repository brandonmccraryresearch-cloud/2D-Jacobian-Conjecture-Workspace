import sympy as sp
from pathlib import Path

a1,a2,a3,a4=sp.symbols('a1 a2 a3 a4'); A=[1,a1,a2,a3,a4,1]; B=[1]+[None]*7
for n in range(1,8):
    known=sum((1+2*(n-i)-3*i)*A[i]*B[n-i] for i in range(1,6) if 0<=n-i<=7)
    B[n]=sp.cancel(-known/(1+2*n))
res=[]
for n in range(8,13):
    s=sum((1+2*(n-i)-3*i)*A[i]*B[n-i] for i in range(6) if 0<=n-i<=7)
    num,_=sp.together(s).as_numer_denom()
    if num != 0: res.append(sp.Poly(num,a1,a2,a3,a4,domain=sp.QQ).as_expr())
# Use Singular-compatible rational expressions.
out=['// Exact characteristic-zero B2.6 reduced system', 'ring R = 0, (a1,a2,a3,a4), dp;']
for i,r in enumerate(res): out.append(f'poly r{i} = {sp.sstr(r)};')
out += [
'option(redSB);',
'ideal I = r0,r1,r2,r3;',
'print("groebner start");',
'ideal G = std(I);',
'print("groebner done");',
'print(size(G));',
'print(G);',
'poly R1 = resultant(r0,r1,a1);',
'poly R2 = resultant(r0,r2,a1);',
'poly R3 = resultant(r0,r3,a1);',
'print("R done");',
'poly S1 = resultant(R1,R2,a2);',
'poly S2 = resultant(R1,R3,a2);',
'print("S done");',
'poly T = resultant(S1,S2,a3);',
'print("T degree: "+string(deg(T)));',
'print("T factor: "+string(factorize(T)));',
'quit;']
Path('/home/ubuntu/gghv/m5_b2_6_char0.sing').write_text('\n'.join(out)+'\n')
print('wrote',len(out),'lines', 'residuals',len(res))
