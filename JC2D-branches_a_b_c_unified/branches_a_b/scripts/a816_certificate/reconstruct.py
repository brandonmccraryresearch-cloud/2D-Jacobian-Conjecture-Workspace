"""reconstruct.py -- multi-modular reconstruction of the a_{8,16} certificate over K5 = Q[w]/(R).

Input : modp/cert_<p>.txt, one file per inert prime p (R irreducible mod p, so F_p[w]/(R) = F_{p^5}), each the
        term-by-term dump of Singular's liftstd transformation matrix T with sum_k I2[k]*T[k,1] = 1 checked in-ring.
        Line format  k|e_1,...,e_56|c   with c an element of F_p[w]/(R) printed as a polynomial of degree <= 4 in w.
Output: cert_K5_candidate.json : {"vars": [...], "rows": {k: [[exps, [q0..q4]], ...]}} with q_i rational strings,
        or a report of which coefficients have not yet stabilised.

Method: for every (row, monomial) and every w-coordinate, Chinese remaindering over the primes used, then rational
reconstruction (Wang): r/s with |r|, |s| <= sqrt(M/2).  A candidate is accepted only if (a) every coordinate
reconstructs, (b) the reconstruction is unchanged when the last prime is dropped (stability), and (c) it reduces
correctly modulo every held-out prime.  Acceptance here is NOT the proof: the exact identity is checked afterwards by
verify_cert_singular.sing and, independently, verify_cert_flint.py.
usage: python3 reconstruct.py [N_USE]   (default: all primes but 4 held out)"""
import sys, re, glob, json, math
from fractions import Fraction
sys.set_int_max_str_digits(0)

TERM = re.compile(r'([+-]?)([^+-]+)')


def parse_coef(s):
    """'(3*w^4-2/5*w+1)' | 'w' | '-17' -> [c0, c1, c2, c3, c4] as Fractions (exact; integers in char p)."""
    s = s.strip()
    if s.startswith('(') and s.endswith(')'):
        s = s[1:-1]
    c = [Fraction(0)] * 5
    for sign, body in TERM.findall(s):
        body = body.strip()
        if not body:
            continue
        if 'w' in body:
            if '*w' in body:
                num, wpart = body.split('*w', 1)
            else:
                assert body.startswith('w'), body
                num, wpart = '1', body[1:]
            k = int(wpart[1:]) if wpart.startswith('^') else 1
            assert wpart in ('', ) or wpart.startswith('^'), body
        else:
            num, k = body, 0
        assert 0 <= k <= 4, body
        a, _, b = num.partition('/')
        val = Fraction(int(a), int(b) if b else 1)
        c[k] += -val if sign == '-' else val
    return c


def load(path):
    head, rows = None, {}
    for line in open(path):
        line = line.rstrip('\n')
        if line.startswith('#'):
            head = line
            continue
        k, e, c = line.split('|')
        exps = tuple(int(t) for t in e.split(','))
        assert len(exps) == 56 and exps[54] == 0 and exps[55] == 0, (k, e)      # no x, y in the certificate
        key = (int(k), exps)
        assert key not in rows, key
        rows[key] = parse_coef(c)
    return head, rows


def ratrecon(a, m):
    a %= m
    if a == 0:
        return Fraction(0)
    bound = math.isqrt(m // 2)
    r0, r1, s0, s1 = m, a, 0, 1
    while r1 > bound:
        q = r0 // r1
        r0, r1, s0, s1 = r1, r0 - q * r1, s1, s0 - q * s1
    if s1 == 0 or abs(s1) > bound or math.gcd(r1, abs(s1)) != 1:
        return None
    return Fraction(r1, s1)


def crt_all(datasets):
    """datasets: list of (p, rows) -> {key: [(residue, modulus) per coordinate]}"""
    keys = set(datasets[0][1])
    for p, rows in datasets:
        assert set(rows) == keys, f"support differs at p={p} (unlucky prime?)"
    out = {}
    for key in keys:
        acc = []
        for i in range(5):
            r, m = 0, 1
            for p, rows in datasets:
                v = rows[key][i]
                v = (v.numerator * pow(v.denominator, -1, p)) % p
                # combine r mod m with v mod p
                t = ((v - r) * pow(m, -1, p)) % p
                r, m = r + m * t, m * p
            acc.append((r, m))
        out[key] = acc
    return out


def reconstruct(crt):
    res, fails = {}, 0
    for key, acc in crt.items():
        q = [ratrecon(r, m) for r, m in acc]
        if any(x is None for x in q):
            fails += 1
        res[key] = q
    return res, fails


if __name__ == '__main__':
    import os
    files = sorted(f for f in glob.glob('modp/cert_*.txt')                      # completed runs only
                   if os.path.exists(f[:-4] + '.log') and 'DONE ' in open(f[:-4] + '.log').read())
    data = []
    for f in files:
        head, rows = load(f)
        p = int(head.split()[-1])
        data.append((p, rows))
    n_use = int(sys.argv[1]) if len(sys.argv) > 1 else len(data) - 4
    use, held = data[:n_use], data[n_use:]
    print(f"primes available {len(data)}, used {len(use)}, held out {len(held)}; terms per prime {len(data[0][1])}")
    crt = crt_all(use)
    rec, fails = reconstruct(crt)
    crt_m1 = crt_all(use[:-1])
    rec_m1, fails_m1 = reconstruct(crt_m1)
    unstable = sum(1 for k in rec if rec[k] != rec_m1[k])
    print(f"reconstruction failures: {fails} (with one prime fewer: {fails_m1}); changed when dropping the last prime: {unstable}")
    # held-out check
    bad_held = 0
    for p, rows in held:
        for key, q in rec.items():
            if any(x is None for x in q):
                continue
            for i in range(5):
                v = rows[key][i]
                lhs = (v.numerator * pow(v.denominator, -1, p)) % p
                rhs = (q[i].numerator * pow(q[i].denominator, -1, p)) % p if q[i].denominator % p else None
                if lhs != rhs:
                    bad_held += 1
    print(f"held-out mismatches: {bad_held}")
    heights = [max(abs(x.numerator).bit_length(), x.denominator.bit_length()) for q in rec.values() for x in q if x is not None]
    print(f"max height (bits) among reconstructed coordinates: {max(heights)}; modulus bits {sum(p.bit_length() for p, _ in use)}")
    dens = set(x.denominator for q in rec.values() for x in q if x is not None)
    lcm = 1
    for d in dens:
        lcm = lcm * d // math.gcd(lcm, d)
    print(f"distinct denominators: {len(dens)}; lcm of denominators has {len(str(lcm))} digits; factor sample: {sorted(dens, key=lambda d: -d)[:3]}")
    if fails == 0 and unstable == 0 and bad_held == 0:
        out = {"vars": None, "rows": {}}
        for (k, exps), q in sorted(rec.items()):
            out["rows"].setdefault(str(k), []).append([list(exps[:54]), [str(x) for x in q]])
        json.dump(out, open('cert_K5_candidate.json', 'w'))
        print("ACCEPTED candidate -> cert_K5_candidate.json (still to be verified exactly)")
    else:
        print("NOT accepted: more primes needed")
