"""Step 1: derive the coefficient-recursion reductions for the B2.2 top-layer system.

System: E_n = sum_{i+k=n} (1+2k-3i) a_i b_k = 0, n=1..16,
  a_0=1, b_10=1, a_i=0 (i>7), b_k=0 (k>10); unknowns a_1..a_7, b_0..b_9 over K5.
Torus: a_7^3 * b_0^2 = 1.

Recursion: E_1..E_9 are linear in b_n (coeff 1+2n != 0) -> b_1..b_9 as
polynomials in (a_1..a_7, b_0). Then E_10..E_16 + torus = 8 equations
in 8 unknowns (a_1..a_7, b_0). Inspect structure.
"""
import sympy as sp
from fractions import Fraction

w = sp.Symbol('w')
R = w**5 - w**4 + 3*w**3 + 3*w**2 + 26
a = sp.symbols('a1:8')   # a1..a7
b0 = sp.Symbol('b0')

def red_w(expr):
    """Reduce w-powers >=5 using R (treat as poly in w)."""
    p = sp.Poly(expr, w)
    if p is None:
        return sp.sympify(expr)
    r = p.rem(sp.Poly(R, w))
    return r.as_expr()

# b[0]=b0, b[10]=1; b[n] for n=1..9 via E_n
b = {0: b0, 10: sp.Integer(1)}
ad = {0: sp.Integer(1)}
for i, s in enumerate(a, start=1):
    ad[i] = s

for n in range(1, 10):
    # E_n = (1+2n)*b_n + sum_{i=1..min(7,n)} (1+2(n-i)-3i) a_i b_{n-i} = 0
    s = sp.Integer(0)
    for i in range(1, min(7, n) + 1):
        k = n - i
        if k < 0 or k > 10:
            continue
        bk = b.get(k, sp.Integer(0))
        s += (1 + 2*k - 3*i) * ad[i] * bk
    bn = -s / (1 + 2*n)
    b[n] = sp.expand(bn)
    b[n] = red_w(b[n])

print("b-recursion done. Degrees in (a's,b0):")
for n in range(1, 10):
    bn = b[n]
    # total degree ignoring w
    terms = sp.Poly(bn, *a, b0).terms() if bn != 0 else []
    deg = max((sum(e for e in exps) for exps, _ in terms), default=0)
    nterms = len(terms)
    print(f"  b_{n}: deg={deg}, terms={nterms}")

# E_n for n=10..16 in (a1..a7, b0)
E = {}
for n in range(10, 17):
    s = sp.Integer(0)
    for i in range(0, 8):
        k = n - i
        if k < 0 or k > 10:
            continue
        ai = ad[i]
        bk = b.get(k, sp.Integer(0))
        s += (1 + 2*k - 3*i) * ai * bk
    E[n] = red_w(sp.expand(s))

torus = red_w(sp.expand(a[6]**3 * b0**2 - 1))  # a7 = a[6]

print("\nReduced system E_10..E_16 + torus: degrees and term counts")
for n in range(10, 17):
    p = sp.Poly(E[n], *a, b0)
    terms = p.terms() if p else []
    # degree in a's+b0 (ignore w)
    deg = 0
    for exps, coeff in terms:
        # exps covers (*a, b0, w)? Poly(gens) with gens=(*a,b0) treats w inside coeff
        deg = max(deg, sum(exps))
    print(f"  E_{n}: deg={deg}, terms={len(terms)}")
p = sp.Poly(torus, *a, b0)
print(f"  torus: deg={max(sum(e) for e,_ in p.terms())}, terms={len(p.terms())}")

# Save the reduced system for step 2
import pickle
sp.save = None
data = {'E': {n: str(E[n]) for n in E}, 'torus': str(torus)}
with open('/tmp/reduced_system.json', 'w') as f:
    import json
    json.dump(data, f)
print("\nsaved to /tmp/reduced_system.json")
