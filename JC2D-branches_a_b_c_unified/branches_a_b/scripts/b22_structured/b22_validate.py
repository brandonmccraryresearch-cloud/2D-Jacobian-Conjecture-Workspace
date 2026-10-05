"""b22_validate.py (run from anywhere: python3 b22_validate.py) -- exact checks of CAIC's B2.2 (c-recursion) system against the repository's K5 chart point.

B2.2 is the m = 7 Lean chart system (BranchAbChart.lean, ChartClassification): unknowns a1..a7, b0..b9 with
a0 = b10 = 1, the sixteen equations E_n = sum_{i+k=n} (1 + 2k - 3i) a_i b_k = 0 (n = 1..16) and a7^3 b0^2 = 1.
1. Rebuild c_n (c_0 = 1, (1+2n) c_n + sum_{i=1}^{min(7,n)} (1 + 2(n-i) - 3i) a_i c_{n-i} = 0) with exact rational
   polynomial arithmetic and compare with CAIC's c_poly.json and b22_6var_system.json (a7 = s^2).
2. Substitute the exact K5 chart point (lean/certgen/chartpoint.json: P = alpha, Q = beta) and check
   E_1..E_16 = 0, a7^3 b0^2 = 1, c_11..c_16 = 0, b0 c_10 = 1, a7^3 = c_10^2, and s := c_10 / a7 with s^2 = a7, s^3 = c_10.
3. Spurious solutions of the 7 x 7 system without a7 != 0: the origin, and the m = 5 points (a6 = a7 = 0)."""
import sys, json, re
import sympy as sp
import flint
import k5 as K
sys.set_int_max_str_digits(0)
import os
BAB = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))   # branches_a_b/
a = sp.symbols("a1:8")            # a1..a7
s = sp.Symbol("s")
A = [sp.Integer(1)] + list(a)     # A[0] = 1

# ---- 1. c-recursion, exact
c = [sp.Integer(1)]
for n in range(1, 17):
    acc = sum((1 + 2 * (n - i) - 3 * i) * A[i] * c[n - i] for i in range(1, min(7, n) + 1))
    c.append(sp.expand(-acc / (1 + 2 * n)))
cp = json.load(open(BAB + "/scripts/b22_structured/c_poly.json"))
print("c_poly.json keys:", sorted(cp)[:10])
ok_c = True
for n in range(10, 17):
    key = next((k for k in cp if re.fullmatch(rf"(c_?)?{n}", k)), None)
    theirs = sp.sympify(cp[key], locals={f"a{i}": a[i - 1] for i in range(1, 8)})
    same = sp.expand(theirs - c[n]) == 0
    ok_c &= same
    print(f"c_{n}: degree {sp.Poly(c[n], *a).total_degree()}, {len(sp.Poly(c[n], *a).terms())} terms; equals c_poly.json[{key}]: {same}")
sysj = json.load(open(BAB + "/scripts/b22_structured/b22_6var_system.json"))
loc = {f"a{i}": a[i - 1] for i in range(1, 7)}; loc["s"] = s
for n in range(11, 17):
    theirs = sp.sympify(sysj[f"c{n}_s"], locals=loc)
    print(f"c{n}_s == c_{n}(a7 = s^2): {sp.expand(theirs - c[n].subs(a[6], s**2)) == 0}")
tor = sp.sympify(sysj["torus_s"], locals=loc)
print("torus_s == s^6 - c_10(a7 = s^2)^2:", sp.expand(tor - (s**6 - c[10].subs(a[6], s**2) ** 2)) == 0)
odd = [n for n in range(10, 17) if any(m[6] % 2 for m in sp.Poly(c[n].subs(a[6], s**2), *a[:6], s).monoms())]
print("odd powers of s after a7 = s^2:", odd or "none")

# ---- 2. the K5 chart point
cpnt = json.load(open(BAB + "/lean/certgen/chartpoint.json"))
def k5v(lst):
    vals = [flint.fmpq(*map(int, x.split("/"))) if "/" in x else flint.fmpq(int(x)) for x in lst]
    return tuple(vals + [flint.fmpq(0)] * (5 - len(vals)))
al = [k5v(cpnt["P"][str(i)]) for i in range(8)]
be = [k5v(cpnt["Q"][str(k)]) for k in range(11)]
assert al[0] == K.ONE5 and be[10] == K.ONE5
E = []
for n in range(0, 18):
    t = K.ZERO5
    for i in range(0, 8):
        k = n - i
        if 0 <= k <= 10:
            t = K.add(t, K.smul(flint.fmpq(1 + 2 * k - 3 * i), K.mul(al[i], be[k])))
    E.append(t)
print("E_0 = b0 (the free constant):", E[0] == be[0])
print("E_1..E_16 all zero at the chart point:", all(K.iszero(E[n]) for n in range(1, 17)), "; E_17 =", "0" if K.iszero(E[17]) else "nonzero")
a7, b0 = al[7], be[0]
torus = K.mul(K.mul(K.mul(a7, a7), a7), K.mul(b0, b0))
print("a7^3 b0^2 == 1:", torus == K.ONE5)
# c_n at the point: rebuild numerically in K5 with the same recursion
cv = [K.ONE5]
for n in range(1, 17):
    acc = K.ZERO5
    for i in range(1, min(7, n) + 1):
        acc = K.add(acc, K.smul(flint.fmpq(1 + 2 * (n - i) - 3 * i), K.mul(al[i], cv[n - i])))
    cv.append(K.smul(flint.fmpq(-1, 1 + 2 * n), acc))
print("c_11..c_16 all zero at the point:", all(K.iszero(cv[n]) for n in range(11, 17)))
print("b_k == b0 c_k for k = 0..9:", all(K.mul(b0, cv[k]) == be[k] for k in range(10)))
print("b0 c_10 == 1:", K.mul(b0, cv[10]) == K.ONE5)
print("a7^3 == c_10^2:", K.mul(K.mul(a7, a7), a7) == K.mul(cv[10], cv[10]))
sK = K.div(cv[10], a7)
print("s := c_10 / a7 in K5:  s^2 == a7:", K.mul(sK, sK) == a7, "; s^3 == c_10:", K.mul(K.mul(sK, sK), sK) == cv[10])
print("s =", K.to_str(sK)[:200], "... (height", K.height_digits(sK), "digits)")
json.dump({"s": [str(x) for x in sK], "a": {str(i): [str(x) for x in al[i]] for i in range(8)}},
          open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "b22_s_point.json"), "w"), indent=1)   # next to this script

# ---- 3. spurious solutions of the 7x7 system (no a7 != 0)
zero = {v: 0 for v in a}
print("origin solves c_11..c_16 = 0 and a7^3 = c_10^2:", all(c[n].subs(zero) == 0 for n in range(11, 17)) and (a[6] ** 3 - c[10] ** 2).subs(zero) == 0)
# m = 5 points: A = (1, a1(a4), a2(a4), a3(a4), a4, 1, 0, 0) with T(a4) = 0; check c_10..c_16 = 0 mod T
x = sp.Symbol("x")
T = sp.Poly(9 * x**10 + 37200 * x**5 + 95051008, x, domain="QQ")
inv_x = sp.invert(x, T.as_expr(), x)                     # x^-1 mod T
def red(e): return sp.Poly(sp.expand(e), x, domain="QQ").rem(T).as_expr()
a1v = red((3 * x**5 + 13078) * inv_x / 362)
a2v = red(3 * (5 * x**5 + 10816) * inv_x**2 / 181)
a3v = red(7 * (123 * x**5 + 70304) * inv_x**3 / 2172)
sub5 = {a[0]: a1v, a[1]: a2v, a[2]: a3v, a[3]: x, a[4]: 1, a[5]: 0, a[6]: 0}
cc5 = [sp.Integer(1)]
for n in range(1, 17):
    acc = sum((1 + 2 * (n - i) - 3 * i) * sub5[a[i - 1]] * cc5[n - i] for i in range(1, min(7, n) + 1))
    cc5.append(red(-acc / (1 + 2 * n)))
print("m = 5 points (a5 = 1, a6 = a7 = 0): c_8..c_16 == 0 mod T:", all(cc5[n] == 0 for n in range(8, 17)), "; c_7 != 0:", cc5[7] != 0)
print("=> the 7x7 system without a7 != 0 has positive-dimensional spurious components (torus orbits of m = 1, 3, 5 points)")

# ---- 4. CAIC's key identity, symbolically: with b_k = b0 c_k (k <= 9), b10 = 1, delta = 1 - b0 c_10,
#         E_n = (51 - 3n) a_{n-10} delta - b0 sum_{k=11}^{n} (1 + 2k - 3(n-k)) a_{n-k} c_k   (n = 10..16)
b0s = sp.Symbol("b0")
bk = [b0s * c[k] for k in range(10)] + [sp.Integer(1)]
delta = 1 - b0s * c[10]
Aext = lambda i: A[i] if 0 <= i <= 7 else 0
okid = True
for n in range(10, 17):
    En = sum((1 + 2 * k - 3 * (n - k)) * Aext(n - k) * bk[k] for k in range(0, 11) if 0 <= n - k <= 7)
    rhs = (51 - 3 * n) * Aext(n - 10) * delta - b0s * sum((1 + 2 * k - 3 * (n - k)) * Aext(n - k) * c[k] for k in range(11, n + 1))
    okid &= sp.expand(En - rhs) == 0
print("key identity E_n = (51-3n) a_{n-10} delta - b0 sum_{k=11}^n (1+2k-3(n-k)) a_{n-k} c_k for n = 10..16:", okid)
