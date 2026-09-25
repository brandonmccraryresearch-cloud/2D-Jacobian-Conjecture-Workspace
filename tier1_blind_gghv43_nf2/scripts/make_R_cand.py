"""
make_R_cand.py -- CANDIDATE quintic R(u) (u = a_2_2^7) from the mod-p eliminants in e5mod/*.json,
by CRT + rational reconstruction.  Writes R_cand.gp for PARI.  R is used only (a) to choose the
msolve prime and (b) for the explicit (exactly verified) data of e5_exact_K5.py; the proof of the
Theorem does not depend on R.
Checks stability: reconstruction from the first half of the primes must equal that from all.
"""
import json, glob
from fractions import Fraction
from crt_recon import ratrec, crt_pair

files = sorted(glob.glob("e5mod/p*.json"))
data = [json.load(open(f)) for f in files]
data = [d for d in data if d["p"] > 10**6]


def recon(ds):
    out = []
    for i in range(0, 36, 7):
        a, m = 0, 1
        for d in ds:
            a, m = crt_pair(a, m, d["data"]["_elim"][i], d["p"])
        out.append(ratrec(a, m))
    return out


full = recon(data)
half = recon(data[: len(data) // 2])
assert all(c is not None for c in full) and full == half, "R reconstruction not stable"
assert all(d["data"]["_elim"][i] == 0 for d in data for i in range(36) if i % 7), "eliminant not a polynomial in a_2_2^7"
open("R_cand.gp", "w").write("R = " + "+".join(f"({c})*u^{i}" for i, c in enumerate(full)) + ";\n")
print("R reconstructed from", len(data), "primes (stable with", len(data) // 2, "), max bits:",
      max(max(abs(c.numerator).bit_length(), c.denominator.bit_length()) for c in full))
