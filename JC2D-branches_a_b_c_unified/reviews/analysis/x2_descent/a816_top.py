"""a816_top.py SRC P W0 OUT -- the K5 top layer of a816_full.sing reduced modulo P at the root W0 of R, as JSON
(alpha_0..alpha_7, beta_0..beta_10) for x2_descent_rigidity.py --top."""
import json, re, sys
src, p, w0, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
R = lambda w: (w**5 - w**4 + 3*w**3 + 3*w**2 + 26) % p
assert R(w0) == 0, "W0 is not a root of R mod P"
txt = open(src).read()
def coeffs(polyname):
    body = re.search(r"poly %s = (.*?);" % polyname, txt, re.S).group(1)
    res = {}
    for m in re.finditer(r"\(\(([^()]*?)\)\*w\^0\+\(([^()]*?)\)\*w\^1\+\(([^()]*?)\)\*w\^2\+\(([^()]*?)\)\*w\^3\+\(([^()]*?)\)\*w\^4\)\*x\^(\d+)\*y\^(\d+)", body):
        val = 0
        for k in range(5):
            num, den = m.group(k + 1).split("/")
            val = (val + int(num) * pow(int(den), -1, p) * pow(w0, k, p)) % p
        res[(int(m.group(6)), int(m.group(7)))] = val
    return res
cP, cQ = coeffs("P"), coeffs("Q")
m, n = 7, 10
alpha = [cP[(i, 2*i - 2)] for i in range(1, m + 2)]
beta = [cQ[(i, 2*i - 3)] for i in range(2, n + 3)]
assert len(cP) == m + 1 and len(cQ) == n + 1, (len(cP), len(cQ))
json.dump({"p": p, "w0": w0, "alpha": alpha, "beta": beta, "lam": 1, "source": "a816_full.sing"}, open(out, "w"))
print("alpha", alpha); print("beta", beta)
