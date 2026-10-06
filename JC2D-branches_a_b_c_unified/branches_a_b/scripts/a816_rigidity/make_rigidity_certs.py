"""make_rigidity_certs.py -- write out the certificates behind the paper's Remark `rem:full-rigidity`.

The remark says that at the K5 point every one of the 51 unknowns (the non-constant lower coefficients of P and Q) is
nilpotent modulo the layer ideal I = (e_1, ..., e_75).  Until 2026-10-06 it rested on one exact rank computation
(14 of 14) inside ../a816_certificate/structured_cert.py.  This script writes the certificates out:

  * 47 pivot certificates   x - phi(x) = sum_k D_x[k] e_k        (one per pivot unknown x), and
  * 14 monomial certificates   m = sum_k H_m[k] e_k             (one per monomial m of depth 4 in the free unknowns
                                                                 tau = (b_11_20, b_12_22), depth 1, and
                                                                 sigma = (a_8_16, b_11_21), depth 2),

all identities of polynomials over K5 = Q[w]/(R).  Each is checked here with the generator's own exact arithmetic
(k5.py), and is meant to be checked again by the independent check_rigidity_flint.py.

Output (OUTDIR): pivot_<x>.json and mono_<m>.json, each {"kind", "target", "rows"}; polynomials are lists of
[[variable names, with repetition], [c0, c1, c2, c3, c4]] (exact rationals as strings, coefficients of 1, w, ..., w^4).
"target" is x - phi(x) (with "phi": phi(x) given separately) or the monomial m.  "rows" maps the generator label "i,j"
(the coefficient of x^i y^j in J) to its cofactor.  Plus MANIFEST.sha256.
structured_cert.py runs in a temporary copy, because it writes into its working directory.
usage: python3 make_rigidity_certs.py ../a816_certificate OUTDIR
"""
import sys, os, json, runpy, shutil, tempfile, time, hashlib

sys.set_int_max_str_digits(0)
A816, OUTDIR = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2])
os.makedirs(OUTDIR, exist_ok=True)
TMP = tempfile.mkdtemp(prefix="a816_rigidity_")
for f in ("structured_cert.py", "k5.py", "a816_system.py", "a816_full.sing", "gens_0.txt", "layers.py"):
    shutil.copy(os.path.join(A816, f), TMP)
os.chdir(TMP)
sys.path.insert(0, TMP)
t0 = time.time()
g = runpy.run_path(os.path.join(TMP, "structured_cert.py"))
print(f"structured_cert.py ran in {time.time() - t0:.0f}s")
K, J, NAMES, DEPTH = g["K"], g["J"], g["NAMES"], g["DEPTH"]
phi, D, FREE = g["phi"], g["D"], g["FREE"]
M4, cols, phig, cert_diff, padd, pmul = g["M4"], g["cols"], g["phig"], g["cert_diff"], g["padd"], g["pmul"]
var = g["var"]


def ser(poly):
    return [[[NAMES[v] for v in m], [str(c) for c in cf]] for m, cf in sorted(poly.items())]


def label(k):
    return f"{k[0]},{k[1]}"


def check(target, cert):
    s = {}
    for k, h in cert.items():
        s = padd(s, pmul(h, J[k]))
    return s == target


def write(name, obj):
    path = os.path.join(OUTDIR, name)
    with open(path, "w") as fh:
        json.dump(obj, fh)
    return path


written = []
# ---- 47 pivot certificates
pivots = [x for x in NAMES if x in D and D[x]]
assert len(pivots) == 47 and sorted(FREE) == sorted(["b_11_20", "b_12_22", "a_8_16", "b_11_21"]), (len(pivots), FREE)
nterms_piv = 0
for x in pivots:
    target = padd(var(x), phi[x], K.k5(-1))
    assert check(target, D[x]), f"pivot certificate for {x} fails"
    nterms_piv += sum(len(h) for h in D[x].values())
    written.append(write(f"pivot_{x}.json", {"kind": "pivot", "unknown": x, "depth": DEPTH[x], "phi": ser(phi[x]),
                                              "target": ser(target),
                                              "rows": {label(k): ser(h) for k, h in sorted(D[x].items())}}))
print(f"47 pivot certificates x - phi(x) = sum_k D_x[k] e_k: all hold; {nterms_piv} cofactor terms")
# ---- 14 monomial certificates (all monomials of depth 4 in the free unknowns)
rowidx = {m: i for i, m in enumerate(M4)}
n = len(cols)
Mat = [[K.ZERO5] * (n + len(M4)) for _ in M4]
for j, (k, mm) in enumerate(cols):
    for m, c in pmul({mm: K.ONE5}, phig[k]).items():
        Mat[rowidx[m]][j] = c
for t, m in enumerate(M4):
    Mat[rowidx[m]][n + t] = K.ONE5
Rr, pivr = K.rref(Mat, n + len(M4))
assert all(p < n for p in pivr) and len(pivr) == len(M4) == 14, "the depth-4 products must span all 14 monomials"
nterms_mono, hmax = 0, 0
for t, m in enumerate(M4):
    hprime = {}
    for i, pc in enumerate(pivr):
        val = Rr[i][n + t]
        if not K.iszero(val):
            k, mm = cols[pc]
            hprime[k] = padd(hprime.get(k, {}), {mm: val})
    H = {}
    for k, h in hprime.items():
        H[k] = padd(H.get(k, {}), h)
        for kk, hh in cert_diff(J[k]).items():
            H[kk] = padd(H.get(kk, {}), pmul(h, hh), K.k5(-1))
    H = {k: h for k, h in H.items() if h}
    target = {m: K.ONE5}
    assert check(target, H), f"monomial certificate for {m} fails"
    nterms_mono += sum(len(h) for h in H.values())
    hmax = max(hmax, max(K.height_digits(c) for h in H.values() for c in h.values()))
    name = "_".join(NAMES[v] for v in m)
    written.append(write(f"mono_{name}.json", {"kind": "monomial", "monomial": [NAMES[v] for v in m],
                                                "target": ser(target),
                                                "rows": {label(k): ser(h) for k, h in sorted(H.items())}}))
print(f"14 monomial certificates m = sum_k H_m[k] e_k (all depth-4 monomials in {FREE}): all hold; "
      f"{nterms_mono} cofactor terms, heights up to {hmax} digits")
with open(os.path.join(OUTDIR, "MANIFEST.sha256"), "w") as fh:
    for p in sorted(written):
        fh.write(hashlib.sha256(open(p, "rb").read()).hexdigest() + "  " + os.path.basename(p) + "\n")
tot_bytes = sum(os.path.getsize(p) for p in written)
print(f"wrote {len(written)} files ({tot_bytes / 1e6:.1f} MB) and MANIFEST.sha256 in {time.time() - t0:.0f}s")
shutil.rmtree(TMP)
