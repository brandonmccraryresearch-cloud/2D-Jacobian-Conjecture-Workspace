"""
crt_recon.py -- CANDIDATE generation only: CRT + rational reconstruction of the mod-p
lex bases in e5mod/*.json.  Nothing produced here is trusted; the exact verification
is done separately (verify_e5.py).
usage: python3 crt_recon.py N_PRIMES_TO_USE out.json
"""
import json, glob, sys
from fractions import Fraction
from math import isqrt


def ratrec(a, m):
    """rational reconstruction of a mod m (Wang), returns Fraction or None."""
    a %= m
    bound = isqrt(m // 2)
    r0, r1 = m, a
    s0, s1 = 0, 1
    while r1 > bound:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        s0, s1 = s1, s0 - q * s1
    if s1 == 0 or abs(s1) > bound:
        return None
    return Fraction(r1, s1) if s1 > 0 else Fraction(-r1, -s1)


def crt_pair(a1, m1, a2, m2):
    t = ((a2 - a1) * pow(m1, -1, m2)) % m2
    return a1 + m1 * t, m1 * m2


if __name__ == "__main__":
    files = sorted(glob.glob("e5mod/p*.json"))
    n = int(sys.argv[1])
    data = [json.load(open(f)) for f in files][:n]
    keys = sorted(data[0]["data"].keys())
    out, ok = {}, True
    for k in keys:
        L = max(len(d["data"][k]) for d in data)
        coeffs = []
        for i in range(L):
            a, m = 0, 1
            for d in data:
                c = d["data"][k][i] if i < len(d["data"][k]) else 0
                a, m = crt_pair(a, m, c, d["p"])
            r = ratrec(a, m)
            if r is None:
                ok = False
                coeffs.append(None)
            else:
                coeffs.append([r.numerator, r.denominator])
        out[k] = coeffs
    print("primes used:", len(data), " all coefficients reconstructed:", ok)
    maxbits = max((abs(c[0]).bit_length() + c[1].bit_length()) for v in out.values() for c in v if c)
    print("max numerator+denominator bits:", maxbits, " vs modulus bits:", sum(d['p'].bit_length() for d in data))
    json.dump(out, open(sys.argv[2], "w"))
