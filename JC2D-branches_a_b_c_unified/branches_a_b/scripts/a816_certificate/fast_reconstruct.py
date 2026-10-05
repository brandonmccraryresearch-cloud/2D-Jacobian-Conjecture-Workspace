"""fast_reconstruct.py [N_USE] -- multimodular reconstruction of Singular's liftstd certificate (all 2967 terms).
Same acceptance rules as reconstruct.py (every coordinate reconstructs, unchanged when the last 8 primes are dropped,
consistent with every held-out prime), but CRT is a dot product with a precomputed basis:
  x = sum_i r_i * c_i  mod M,   c_i = (M/p_i) * ((M/p_i)^(-1) mod p_i).
Acceptance is NOT the proof; verify_cert_flint.py and the Singular check decide."""
import sys, os, glob, json, math, time
from fractions import Fraction
from reconstruct import load, ratrecon
sys.set_int_max_str_digits(0)
t0 = time.time()
files = sorted(f for f in glob.glob('modp/cert_*.txt') if os.path.exists(f[:-4] + '.log') and 'DONE ' in open(f[:-4] + '.log').read())
data = [(int(h.split()[-1]), rows) for h, rows in (load(f) for f in files)]
n_use = int(sys.argv[1]) if len(sys.argv) > 1 else len(data) - 8
use, held = data[:n_use], data[n_use:n_use + 8]          # 8 held-out primes
keys = sorted(data[0][1])
for p, rows in data:
    assert sorted(rows) == keys, f"support differs at p={p}"
print(f"primes: {len(data)} completed, {len(use)} used, {len(held)} held out; {len(keys)} terms; load {time.time()-t0:.0f}s")


def basis(primes):
    M = math.prod(primes)
    return M, [(M // p) * pow(M // p, -1, p) for p in primes]


def residues(rows_list, primes, key, i):
    out = []
    for (p, rows) in rows_list:
        v = rows[key][i]
        out.append((v.numerator * pow(v.denominator, -1, p)) % p)
    return out


def recon(rows_list):
    primes = [p for p, _ in rows_list]
    M, C = basis(primes)
    res, fails = {}, 0
    for key in keys:
        q = []
        for i in range(5):
            r = sum(a * c for a, c in zip(residues(rows_list, primes, key, i), C)) % M
            q.append(ratrecon(r, M))
        if any(x is None for x in q):
            fails += 1
        res[key] = q
    return res, fails


rec, fails = recon(use)
print(f"reconstruction with {len(use)} primes: failures {fails}  ({time.time()-t0:.0f}s)")
rec2, fails2 = recon(use[:-8])
unstable = sum(1 for k in keys if rec[k] != rec2[k])
print(f"with 8 primes fewer: failures {fails2}; entries that change: {unstable}  ({time.time()-t0:.0f}s)")
bad = 0
for p, rows in held:
    for key in keys:
        for i in range(5):
            x = rec[key][i]
            if x is None or x.denominator % p == 0:
                bad += 1
                continue
            v = rows[key][i]
            if (x.numerator * pow(x.denominator, -1, p)) % p != (v.numerator * pow(v.denominator, -1, p)) % p:
                bad += 1
print(f"held-out mismatches: {bad}")
if fails == 0 and unstable == 0 and bad == 0:
    hmax = max(max(len(str(abs(x.numerator))), len(str(x.denominator))) for q in rec.values() for x in q)
    from a816_system import NAMES
    out = {"vars": NAMES + ["z"], "rows": {}}
    for (k, exps), q in sorted(rec.items()):
        out["rows"].setdefault(str(k), []).append([list(exps[:54]), [str(x) for x in q]])
    json.dump(out, open('liftstd_cert_K5.json', 'w'))
    print(f"ACCEPTED: liftstd_cert_K5.json, max height {hmax} digits  ({time.time()-t0:.0f}s)")
else:
    print("NOT accepted")
