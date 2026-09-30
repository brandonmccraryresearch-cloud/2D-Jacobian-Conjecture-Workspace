"""Chart generators of lower_c's ideal, built directly from certgen_c/conds_c.json (exact over K5):
   the chart is T2 = 1, S2 = kappa with kappa the double root of Omega (Omega = o1 (S2 - kappa T2^2)^2 is checked).
   Variables of the chart: t, s, r, u, q = T1, S1, R1, R2, Q  (b_11_20, b_11_21, a_6_13, a_7_15, b_10_21).
   Library module (no Singular)."""
import json, sys, os
from flint import fmpq_poly, fmpq
sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
Rr = fmpq_poly([26, 0, 3, 3, -1, 1]); Z = fmpq_poly([0])
V7 = ["b_11_20", "b_12_22", "b_11_21", "b_12_23", "a_6_13", "a_7_15", "b_10_21"]      # T1 T2 S1 S2 R1 R2 Q
NAMES = ["Psi", "Phi1", "Phi2", "Theta1", "Theta2", "Theta3"]
def K(cs): return fmpq_poly([fmpq(*map(int, str(c).split('/'))) if '/' in str(c) else fmpq(int(c)) for c in cs]) % Rr
def kinv(a):
    g, s, _ = a.xgcd(Rr); assert g == 1; return s % Rr
def load7(path=os.path.join(HERE, "..", "certgen_c", "conds_c.json")):
    d = json.load(open(path))
    out = {}
    for n, P in d.items():
        Q = {}
        for m, cs in P:
            e = [0] * 7
            for v, k in m: e[V7.index(v)] += k
            Q[tuple(e)] = K(cs)
        out[n] = Q
    return out
def kappa(C7):
    Om = C7["Omega"]
    o1, o2, o3 = Om[(0, 0, 0, 2, 0, 0, 0)], Om[(0, 2, 0, 1, 0, 0, 0)], Om[(0, 4, 0, 0, 0, 0, 0)]
    assert set(Om) == {(0, 0, 0, 2, 0, 0, 0), (0, 2, 0, 1, 0, 0, 0), (0, 4, 0, 0, 0, 0, 0)}
    assert o1 != 0 and (o2 * o2 - 4 * o1 * o3) % Rr == 0, "Omega is not o1*(S2 - kappa T2^2)^2"
    return (-o2 * kinv(2 * o1)) % Rr
def chart(C7, kap, names=NAMES, t1=None):
    """T2 = 1, S2 = kappa; optionally T1 = t1 (a K5 element).  Keys (t, s, r, u, q), or (s, r, u, q) if t1 is given."""
    out = {}
    for n in names:
        Q = {}
        for e, c in C7[n].items():
            T1, T2, S1, S2, R1, R2, Qv = e
            val = c * kap ** S2
            if t1 is None: key = (T1, S1, R1, R2, Qv)
            else: val = val * t1 ** T1; key = (S1, R1, R2, Qv)
            Q[key] = (Q.get(key, Z) + val) % Rr
        out[n] = {k: v for k, v in Q.items() if v != 0}
    return out
if __name__ == "__main__":
    C7 = load7(); kap = kappa(C7)
    ch = chart(C7, kap)
    # cross-check against the earlier conds_chart.json (explore2.py)
    old = json.load(open(os.path.join(HERE, "..", "conds_chart.json")))
    Vc = ["b_11_20", "b_11_21", "a_6_13", "a_7_15", "b_10_21"]
    for n in NAMES:
        P = {}
        for m, cs in old[n]:
            e = dict(m); P[tuple(e.get(v, 0) for v in Vc)] = K(cs)
        assert {k: v for k, v in P.items() if v != 0} == ch[n], n
    print("chart generators from conds_c.json:", {n: len(ch[n]) for n in NAMES}, "| equal to conds_chart.json: True")
    B = chart(C7, kap, t1=Z)
    print("slice t1 = 0:", {n: len(B[n]) for n in NAMES})
