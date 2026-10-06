"""Step 2: the c-recursion reformulation.

Define c_n by the LINEAR recursion (normalizing b_0=1):
  (1+2n)*c_n + sum_{i=1..min(7,n)} (1+2(n-i)-3i)*a_i*c_{n-i} = 0, c_0=1.
Then E_10..E_16  <=>  b_0*c_10 = 1  and  c_11 = ... = c_16 = 0.
And torus a_7^3*b_0^2=1 with b_0=1/c_10 gives a_7^3 = c_10^2.

So: solve c_11=...=c_16=0, a_7^3-c_10^2=0 in (a_1..a_7), then b_0=1/c_10.
Inspect degrees and structure of c_10..c_16.
"""
import sympy as sp
from fractions import Fraction

a = sp.symbols('a1:8')
ad = {0: sp.Integer(1)}
for i, s in enumerate(a, start=1):
    ad[i] = s

c = {0: sp.Integer(1)}
for n in range(1, 17):
    s = sp.Integer(0)
    for i in range(1, min(7, n) + 1):
        k = n - i
        s += (1 + 2*k - 3*i) * ad[i] * c[k]
    cn = sp.expand(-s / (1 + 2*n))
    c[n] = cn

print("degrees of c_n in (a1..a7):")
for n in range(1, 17):
    p = sp.Poly(c[n], *a)
    terms = p.terms()
    print(f"  c_{n}: deg={p.total_degree()}, terms={len(terms)}")

print()
print("c_1 =", c[1])
print("c_2 =", c[2])
print("c_3 =", c[3])

import json
json.dump({str(n): str(c[n]) for n in range(10, 17)},
          open('/tmp/c_poly.json', 'w'))
print("\nsaved c_10..c_16")
