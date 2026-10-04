# y-reformulation of the Lean chart: y_i = a_{7-i}/a7 (i=1..6), y7 = 1/a7 (a0 = 1).
# Claim: E_1..E_16 = 0 & a7^3 b0^2 = 1  <=>  b_{10-k} = S_k(y) (k=0..10), S_11..S_16 = 0, S_10^2 = y7^3,
# where S_k = [v^k](1 + y1 v + ... + y7 v^7)^{3/2}.
import sympy as sp, json
Y = sp.symbols('y1:8')
def S_list(N):
    f = [sp.Integer(1)]
    for k in range(0, N):
        s = sum(Y[i-1]*(5*i - 2*k - 2)*f[k+1-i] for i in range(1, 8) if k+1-i >= 0)
        f.append(sp.expand(s/(2*(k+1))))
    return f
if __name__ == '__main__':
    S = S_list(17)
    print([len(sp.Add.make_args(s)) for s in S])
    # check against power series directly
    v = sp.symbols('v'); x = sum(Y[i-1]*v**i for i in range(1, 8))
    ser = sp.series((1 + x)**sp.Rational(3, 2), v, 0, 9).removeO()
    print("recursion == series (k<=8):", all(sp.expand(ser.coeff(v, k) - S[k]) == 0 for k in range(9)))
    # check at the K5 Lean-chart point
    from k5 import lean_point
    w = sp.symbols('w'); R = sp.Poly(w**5 - w**4 + 3*w**3 + 3*w**2 + 26, w, domain='QQ')
    P = lean_point()
    el = {k: sp.Poly(sum(sp.Rational(int(c.p), int(c.q))*w**i for i, c in enumerate(v.coeffs())), w, domain='QQ') for k, v in P.items()}
    el['a0'] = sp.Poly(1, w, domain='QQ'); el['b10'] = sp.Poly(1, w, domain='QQ')
    inv_a7 = sp.Poly(sp.invert(el['a7'].as_expr(), R.as_expr(), w), w, domain='QQ')
    yv = {Y[i-1]: (el[f'a{7-i}'] * inv_a7).rem(R) for i in range(1, 7)}; yv[Y[6]] = inv_a7
    def ev(p):
        P = sp.Poly(p, *Y); acc = sp.Poly(0, w, domain='QQ')
        for mon, c in P.terms():
            t = sp.Poly(c, w, domain='QQ')
            for yi, e in zip(Y, mon):
                for _ in range(e): t = (t * yv[yi]).rem(R)
            acc = acc + t
        return acc.rem(R)
    ok_b = all((ev(S[k]) - el[f'b{10-k}']).rem(R).is_zero for k in range(0, 11))
    ok_z = [ev(S[k]).is_zero for k in range(11, 17)]
    print("b_{10-k} = S_k(y) for k=0..10:", ok_b); print("S_11..S_16 vanish:", ok_z)
    print("S_10^2 = y7^3:", (ev(S[10]**2 - Y[6]**3)).is_zero)
    print("S_17 at point (nonzero expected):", ev(S[17]).as_expr())
