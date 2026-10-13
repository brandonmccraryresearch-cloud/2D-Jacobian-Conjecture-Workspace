"""Shim for the bundle's certgen_c/make_cert_c.py, which imports the project's certgen/ (absent from the bundle).

The bundle's gen_t1zero_c.py uses only `Kc` and `mono_mul` from it (2 and 1 call sites). The three definitions below
are copied verbatim from bundle_v3_1/jacobian_lean/certgen_c/make_cert_c.py (lines 21, 23 and 38-41); gen_chart.py
puts this directory first on sys.path so that `import make_cert_c` finds them.
"""
from flint import fmpq_poly, fmpq

Rr = fmpq_poly([26, 0, 3, 3, -1, 1])
def Kc(c): return fmpq_poly([fmpq(*map(int, s.split('/'))) if '/' in s else fmpq(int(s)) for s in c]) % Rr
def mono_mul(m1, m2):
    d = dict(m1)
    for v, e in m2: d[v] = d.get(v, 0) + e
    return tuple(sorted(d.items()))
