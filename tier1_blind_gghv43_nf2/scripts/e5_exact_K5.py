"""
e5_exact_K5.py -- explicit exact E5 solutions ("partial solutions") over K5 = Q[w]/(Rr),
Rr = w^5 - w^4 + 3w^3 + 3w^2 + 26.
Normalisation a_1_0 = b_2_1 = a_2_2 = 1 (t-rescaling of the chart a_8_14 = 1 by theta = a_2_2).
Candidates: from the mod-p lex bases (e5mod/*.json) via u = theta^7 = psi(w), CRT + rational
reconstruction.  VERIFICATION (the only thing that matters): the candidate point is substituted
into all 17 weight -4 equations and reduced mod Rr in exact rational arithmetic (python-flint).
Output: e5_exact_K5.json with the coordinates (5 rational coefficients each, w-basis, low->high).
"""
import json, glob
from fractions import Fraction
from flint import fmpq_poly, fmpq, nmod_poly
from crt_recon import ratrec, crt_pair
from gen_system import build

RR = [26, 0, 3, 3, -1, 1]                       # low -> high
PSI_HI = None
for line in open("psi.out"):
    if line.startswith("PSI "):
        PSI_HI = [Fraction(s) for s in line[4:].strip().strip("[]").split(", ")]
PSI = list(reversed(PSI_HI))                    # low -> high
LP, LQ, eqs, tgt = build()
w_ = lambda ij: ij[1] - 2 * ij[0]
kv = {}
for v in json.load(open(sorted(glob.glob("e5mod/p*.json"))[0]))["data"]:
    if v == "_elim":
        continue
    if v == "lam":
        kv[v] = 0
    else:
        i = int(v.split('_')[1])
        kv[v] = i - 1 if v[0] == 'a' else i - 2

acc = {}
nprimes = 0
for fn in sorted(glob.glob("e5mod/p*.json")):
    d = json.load(open(fn)); p = d["p"]; data = d["data"]
    if p < 10**6:
        continue
    Rp = nmod_poly(RR, p)
    psi = nmod_poly([int(c.numerator * pow(c.denominator, -1, p)) % p for c in PSI], p)
    g_, psi_inv, _ = psi.xgcd(Rp)
    assert g_ == 1 and (psi * psi_inv) % Rp == 1
    for v, h in data.items():
        if v == "_elim":
            continue
        k = kv[v]
        assert all(c == 0 for e, c in enumerate(h) if (e - k) % 7 != 0), (v, "mu7 structure violated")
        # A_v = theta^-k * h_v(theta) = sum_{e = k mod 7} h[e] * u^((e-k)/7); exponents may be -1
        A = nmod_poly([0], p)
        for e in range(k % 7, len(h), 7):
            ex = (e - k) // 7
            term = nmod_poly([h[e]], p)
            base = psi if ex >= 0 else psi_inv
            for _ in range(abs(ex)):
                term = (term * base) % Rp
            A = (A + term) % Rp
        coeffs = [int(A[i]) for i in range(5)]
        for i, c in enumerate(coeffs):
            a0, m0 = acc.get((v, i), (0, 1))
            acc[(v, i)] = crt_pair(a0, m0, c, p)
    nprimes += 1

cand = {}
ok = True
for (v, i), (a, m) in acc.items():
    r = ratrec(a, m)
    if r is None:
        ok = False
    cand.setdefault(v, [None] * 5)[i] = r
print("primes used:", nprimes, " all reconstructed:", ok)
maxbits = max(max(abs(c.numerator).bit_length(), c.denominator.bit_length()) for v in cand for c in cand[v] if c is not None)
print("max bits of numerator/denominator:", maxbits)

# ---------------- exact verification in Q[w]/(Rr)
Rq = fmpq_poly(RR)
K = lambda coeffs: fmpq_poly([fmpq(c.numerator, c.denominator) for c in coeffs]) % Rq
pt = {v: K(cand[v]) for v in cand}
pt["a_2_2"] = fmpq_poly([1]); pt["a_1_0"] = fmpq_poly([1]); pt["b_2_1"] = fmpq_poly([1])
# a_8_14 = theta^-7 = 1/u, u = psi(w)
psiq = fmpq_poly([fmpq(c.numerator, c.denominator) for c in PSI]) % Rq
g, sinv, _ = psiq.xgcd(Rq)
assert g == 1 and (sinv * psiq) % Rq == 1
pt["a_8_14"] = sinv % Rq
nz = 0
for k in eqs:
    if w_(k) != -4:
        continue
    s = fmpq_poly([0])
    for c, pv, qv in eqs[k]:
        s += c * pt[pv] * pt[qv]
    if k == tgt:
        s -= pt["lam"]
    s = s % Rq
    nz += (s != 0)
print("weight -4 equations not vanishing exactly:", nz, "of 17")
print("lam =", pt["lam"], "   a_8_14 =", pt["a_8_14"])
assert nz == 0
outd = {v: [str(c) for c in cand[v]] for v in cand}
outd["a_8_14"] = [str(pt["a_8_14"][i]) for i in range(5)]
outd["_field"] = "Q[w]/(w^5 - w^4 + 3*w^3 + 3*w^2 + 26); normalisation a_1_0=b_2_1=a_2_2=1; coefficient lists low->high in w"
json.dump(outd, open("e5_exact_K5.json", "w"), indent=1)
print("EXACT VERIFICATION PASSED: an explicit solution of the weight -4 block over K5 with a_8_14 != 0")
