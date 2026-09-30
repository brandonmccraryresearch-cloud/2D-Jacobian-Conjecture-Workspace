"""gen_omega_edge.py -- Lean data for Jacobian/BranchC/OmegaEdge.lean:
betaPipe = b_{12,21} of the pipeline top layer (certgen/e5_exact_K5.json, a_{1,0} = a_{2,2} = b_{2,1} = 1),
the cofactor q with kappa(w) * 3 * betaPipe(w) - 1 = q(w) * R(w) in Q[w], and betaPipe(9) mod 101."""
import json, os, sympy as sp
HERE = os.path.dirname(os.path.abspath(__file__))
w = sp.symbols('w'); R = sp.Poly(w**5 - w**4 + 3*w**3 + 3*w**2 + 26, w, domain='QQ')
def P(cs): return sp.Poly(sum(sp.Rational(c) * w**k for k, c in enumerate(cs)), w, domain='QQ')
d = json.load(open(os.path.join(HERE, "..", "certgen", "e5_exact_K5.json")))
beta = P(d["b_12_21"])
pipe = json.load(open(os.path.join(HERE, "omega_pipeline.json")))
c1, c2 = P(pipe["c1"]), P(pipe["c2"])
s_, t_, g = sp.gcdex(c1, R); assert g == sp.Poly(1, w, domain='QQ')
kap = (-c2 * s_ * sp.Rational(1, 2)).rem(R)
q, r = (kap * 3 * beta - 1).div(R); assert r.is_zero
def lean(p):
    cs = p.all_coeffs()[::-1]; terms = []
    for k, c in enumerate(cs):
        c = sp.Rational(c)
        if c == 0: continue
        num = f"(({c.p}) / {c.q} : L)" if c.q != 1 else f"({c.p} : L)"
        terms.append(num + ("" if k == 0 else (" * w" if k == 1 else f" * w ^ {k}")))
    return "(" + " + ".join(terms) + ")" if terms else "(0 : L)"
v9 = sum(sp.Rational(c) * 9**k for k, c in enumerate(beta.all_coeffs()[::-1]))
n, dd = v9.p, v9.q
assert dd % 101 != 0 and (n - 70 * dd) % 101 == 0
out = {"beta": lean(beta), "q": lean(q), "n": str(n), "d": str(dd)}
json.dump(out, open(os.path.join(HERE, "omega_edge_data.json"), "w"))
print("beta digits:", max(len(str(abs(sp.Rational(c).p))) for c in beta.all_coeffs()), " q degree:", q.degree())
