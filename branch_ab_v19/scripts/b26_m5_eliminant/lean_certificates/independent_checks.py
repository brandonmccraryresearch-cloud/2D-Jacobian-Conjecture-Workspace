"""independent_checks.py -- checks of lean/Jacobian/B26* that do not use the generator gen_b26_lean.py (a few seconds).

1. Statement fidelity. Parse the Lean definitions `m5Chart` and `m3Chart` (lean/Jacobian/B26/Defs.lean). Compare
   them with the coefficient equations E_1, ..., E_{n+m} of alpha*beta + u(2 alpha beta' - 3 alpha' beta) = 1 in the
   chart alpha_0 = alpha_m = beta_0 = 1, built here from scratch: E_N = sum_{i+k=N} (1 + 2k - 3i) alpha_i beta_k.
2. The closed forms. Parse `m5T`/`m3T` (Defs.lean) and the relations of `m5_chart_iff`/`m3_chart_iff`
   (lean/Jacobian/B26.lean). At every root of T, solve the relations for a_1, ..., a_{m-2} and E_1..E_n for
   b_1..b_n. Then evaluate every E_N at 60 significant digits and check that the d points are pairwise distinct.
   With vdim = d of the chart ideal (m5_ideal_equality.sing, m3_ideal_equality.sing), this counts the solutions
   independently of Lean: d distinct solutions in a zero-dimensional ideal of vector-space dimension d.
Controls: each check is also run on a perturbed input (one chart equation changed; T shifted by 1) and must fail."""
import os, re, sys
import sympy as sp
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(HERE, "..", "..", "..", "lean", "Jacobian"))
defs = open(os.path.join(LEAN, "B26", "Defs.lean")).read()
umbrella = open(os.path.join(LEAN, "B26.lean")).read()
ok = True


def lean_expr(s, syms):
    return sp.sympify(s.strip().replace("^", "**"), locals=syms)


def lean_chart(name):
    m = re.search(rf"def {name} \(([^)]*)\) : Prop :=\n(.*?)\n\n", defs, re.S)
    args = m.group(1).replace(": L", "").split()
    syms = {v: sp.Symbol(v) for v in args}
    return [sp.expand(lean_expr(c.split("=")[0], syms) - lean_expr(c.split("=")[1], syms))
            for c in m.group(2).split("∧")]


def scratch(m):
    n = (3 * m - 1) // 2
    a = sp.symbols(f"a1:{m}"); b = sp.symbols(f"b1:{n + 1}")
    al = [1] + list(a) + [1]; be = [1] + list(b)
    E = [sp.expand(sum((1 + 2 * k - 3 * i) * al[i] * be[k] for i in range(m + 1) for k in range(n + 1) if i + k == N))
         for N in range(1, n + m + 1)]
    return a, b, E


mp.mp.dps = 60
x = sp.Symbol("x")
for m, chart, tname, iff in ((5, "m5Chart", "m5T", "m5_chart_iff"), (3, "m3Chart", "m3T", "m3_chart_iff")):
    a, b, E = scratch(m)
    L = lean_chart(chart)
    same = len(L) == len(E) and all(sp.expand(p - q) == 0 for p, q in zip(L, E))
    print(f"[1] {chart}: {len(L)} conjuncts; conjunct N == E_N (built from scratch) for N = 1..{len(E)}: {same}")
    ok &= same
    Ep = E[:2] + [E[2] + a[0]] + E[3:]               # control: E_3 perturbed by a_1
    caught = not all(sp.expand(p - q) == 0 for p, q in zip(L, Ep))
    print(f"    control (E_3 + a_1 instead of E_3) detected: {caught}")
    ok &= caught
    # 2. T and the relations, read from the Lean files
    T = lean_expr(re.search(rf"def {tname} \(x : L\) : L := (.*)", defs).group(1), {"x": x})
    stmt = re.search(rf"theorem {iff} \(([^)]*)\) :\n(.*?) := by", umbrella, re.S).group(2)
    syms = {str(s): s for s in a + b}
    rels = []
    for c in stmt.split("↔")[1].strip().strip("()").split("∧"):
        c = c.strip()
        if c.startswith(f"{tname} ") or c.startswith("b"):
            continue
        lhs, rhs = c.split("=")
        rels.append(sp.expand(lean_expr(lhs, syms) - lean_expr(rhs, syms)))
    top = a[m - 2]
    sol = {}
    for r in rels:                                   # each relation is linear in one lower a_k
        k = next(v for v in a[:m - 2] if r.has(v) and sp.degree(r, v) == 1)
        sol[k] = sp.solve(r, k)[0]
    def evaluate(TT):
        roots = sp.Poly(TT, x).nroots(n=60, maxsteps=500)
        worst = 0; pts = []
        for rt in roots:
            sub = {top: rt}
            for k, f in sol.items():
                sub[k] = sp.N(f.subs(top, rt), 60)
            for N in range(1, len(b) + 1):          # E_N = (1 + 2N) b_N + (terms without b_N)
                rest = sp.N(E[N - 1].subs(b[N - 1], 0).subs(sub), 60)
                sub[b[N - 1]] = sp.N(-rest / (1 + 2 * N), 60)
            worst = max([worst] + [abs(complex(sp.N(e.subs(sub), 60))) for e in E])
            pts.append(tuple(complex(sp.N(sub[v], 30)) for v in a))
        return worst, pts
    worst, pts = evaluate(T)
    gap = min(max(abs(p[i] - q[i]) for i in range(len(p))) for p in pts for q in pts if p is not q)
    good = worst < 1e-40 and len(set(pts)) == len(pts) == sp.degree(T, x)
    print(f"[2] {iff}: T of degree {sp.degree(T, x)}; {len(rels)} relations read from the theorem; "
          f"max |E_N| at the {len(pts)} points = {float(worst):.1e}; pairwise distinct (min gap {gap:.3g}): {good}")
    ok &= good
    wc, _ = evaluate(T + 1)                          # control: roots of T + 1 must not solve the chart system
    print(f"    control (roots of T + 1): max |E_N| = {float(wc):.1e}; detected: {wc > 1e-10}")
    ok &= wc > 1e-10
print("ALL INDEPENDENT CHECKS PASSED" if ok else "SOMETHING FAILED")
sys.exit(0 if ok else 1)
