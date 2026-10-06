"""probe_heights.py: CRT + rational reconstruction for a few certificate entries (rows with 1-3 terms) using every
completed prime, to estimate the heights of the char-0 liftstd certificate."""
import glob, os, sys
sys.set_int_max_str_digits(0)
from reconstruct import load, ratrecon
files = sorted(f for f in glob.glob('modp/cert_*.txt') if os.path.exists(f[:-4] + '.log') and 'DONE ' in open(f[:-4] + '.log').read())
data = [(int(h.split()[-1]), rows) for h, rows in (load(f) for f in files)]
if len(sys.argv) > 1:
    data = data[:int(sys.argv[1])]          # first N completed primes (inert_primes.json order is descending; files sort ascending)
keys = sorted(k for k in data[0][1] if k[0] in (1, 5, 9, 76))
print(len(data), "primes;", "modulus bits", sum(p.bit_length() for p, _ in data))
for key in keys:
    out = []
    for i in range(5):
        r, m, hist = 0, 1, []
        for n, (p, rows) in enumerate(data, 1):
            v = rows[key][i]; v = (v.numerator * pow(v.denominator, -1, p)) % p
            t = ((v - r) * pow(m, -1, p)) % p; r, m = r + m * t, m * p
            hist.append(ratrecon(r, m))
        # first n from which the reconstruction is constant to the end
        last = hist[-1]; first = len(hist)
        while first > 1 and hist[first - 2] == last: first -= 1
        stable = last is not None and first < len(hist) - 2
        out.append((first, None if last is None else (len(str(abs(last.numerator))), len(str(last.denominator)))) if stable else ("unstable", None))
    print(key[0], "z^%d" % key[1][53], [o for o in out])
