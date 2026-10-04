"""Validate a candidate B2.2 top-layer point by substitution into all 17 equations.

Candidate: a_1..a_7, b_0 as K5 elements (dict {power: Fraction} or list of 5).
Steps:
  1. b_1..b_9 via b-recursion over K5.
  2. Check E_n = 0 for n=1..16 over K5.
  3. Check torus a_7^3 * b_0^2 = 1 over K5.
"""
import sys
from fractions import Fraction

# K5 arithmetic
def k5_add(a, b): return [x+y for x, y in zip(a, b)]
def k5_sub(a, b): return [x-y for x, y in zip(a, b)]
def k5_mul(a, b):
    c = [Fraction(0)]*9
    for i, x in enumerate(a):
        for j, y in enumerate(b): c[i+j] += x*y
    for k in range(8, 4, -1):
        q = c[k]
        if q: c[k-1]+=q; c[k-2]+=-3*q; c[k-3]+=-3*q; c[k-5]+=-26*q; c[k]=Fraction(0)
    return c[:5]
def k5_eq0(a): return all(x == 0 for x in a)
def k5_pow(a, e):
    r = [Fraction(1), Fraction(0), Fraction(0), Fraction(0), Fraction(0)]
    for _ in range(e): r = k5_mul(r, a)
    return r

def validate(a_list, b0):
    """a_list = [a1..a7] as 5-coord lists, b0 as 5-coord list. Returns True/False."""
    a = {0: [Fraction(1), Fraction(0), Fraction(0), Fraction(0), Fraction(0)]}
    for i, v in enumerate(a_list, start=1):
        a[i] = [Fraction(x) for x in v]
    b = {0: [Fraction(x) for x in b0],
         10: [Fraction(1), Fraction(0), Fraction(0), Fraction(0), Fraction(0)]}
    # b-recursion: E_n = 0 for n=1..9 gives b_n
    for n in range(1, 10):
        s = [Fraction(0)]*5
        for i in range(1, min(7, n)+1):
            k = n-i
            if k < 0 or k > 10: continue
            bk = b.get(k, [Fraction(0)]*5)
            coeff = (1 + 2*k - 3*i)
            # s += coeff * a_i * bk
            t = k5_mul(a[i], bk)
            t = [coeff*x for x in t]
            s = k5_add(s, t)
        # b_n = -s/(1+2n)
        inv = Fraction(1, 1+2*n)
        b[n] = [-inv*x for x in s]
    # Check E_n = 0 for n=1..16
    ok = True
    for n in range(1, 17):
        s = [Fraction(0)]*5
        for i in range(0, 8):
            k = n-i
            if k < 0 or k > 10: continue
            ai = a.get(i, [Fraction(0)]*5)
            bk = b.get(k, [Fraction(0)]*5)
            coeff = (1 + 2*k - 3*i)
            t = k5_mul(ai, bk)
            t = [coeff*x for x in t]
            s = k5_add(s, t)
        if not k5_eq0(s):
            print(f"  E_{n} FAIL: {s}")
            ok = False
    # Torus
    t = k5_mul(k5_pow(a[7], 3), k5_pow(b[0], 2))
    t = k5_sub(t, [Fraction(1), Fraction(0), Fraction(0), Fraction(0), Fraction(0)])
    if not k5_eq0(t):
        print(f"  torus FAIL: {t}")
        ok = False
    return ok

if __name__ == '__main__':
    print("validation module ready")
