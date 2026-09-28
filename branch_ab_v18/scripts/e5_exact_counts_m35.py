"""e5_exact_counts_m35.py -- exact solution counts for the E5 top-layer system at m=3,5.

E5:  E(u) = alpha*beta + u*(2*alpha*beta' - 3*alpha'*beta) = 1,
     E_n = sum_{i+j=n} (1 + 2j - 3i) A_i B_j,  E_0 = 1, E_n = 0 (n >= 1),
with the paper's normalization alpha_0 = beta_0 = alpha_m = 1
(alpha(u) = 1 + a_1 u + ... + a_{m-1} u^{m-1} + u^m,
 beta(u)  = 1 + b_1 u + ... + b_e u^e,  e = (3m-1)/2).

For each m in {3, 5} this script:
  1. builds the normalized E5 system,
  2. asks Singular for vdim (vector-space dimension = #solutions with multiplicity),
  3. eliminates to a univariate polynomial in a_{m-1} and checks it equals the
     paper's stated eliminant up to a nonzero rational scale,
  4. checks the eliminant is irreducible over Q and separable (FLINT),
  5. concludes the EXACT count: irreducible separable eliminant of degree d gives
     d distinct a_{m-1}-values, each realized by a solution, so at least d distinct
     solutions; the Belyi upper bound (Prop 6.1) gives at most d.  Hence exactly d.

Needs: Singular on PATH (or SINGULAR env var), python-flint.
Exit 0 iff every check passes.
"""
import os, re, subprocess, sys

SINGULAR = os.environ.get("SINGULAR", "Singular")

def build(m):
    e = (3 * m - 1) // 2
    assert 3 * m - 1 == 2 * e
    avars = ["a%d" % i for i in range(m - 1, 0, -1)]   # A_0 = A_m = 1
    bvars = ["b%d" % i for i in range(e, 0, -1)]       # B_0 = 1
    def A(i): return "1" if i in (0, m) else "a%d" % i
    def B(j): return "1" if j == 0 else "b%d" % j
    eqs = []
    for n in range(m + e + 1):
        terms = []
        for i in range(m + 1):
            for j in range(e + 1):
                if i + j == n:
                    c = 1 + 2 * j - 3 * i
                    if c:
                        terms.append((c, A(i), B(j)))
        s = ""
        for (c, ai, bj) in terms:
            t = "%s*%s" % (ai, bj) if c == 1 else "%d*%s*%s" % (c, ai, bj)
            s += (" + " if s else "") + t
        if n == 0:
            s += " - 1"
        if s:
            eqs.append(s)
    keep = "a%d" % (m - 1)
    others = [v for v in bvars + avars if v != keep]
    L = ["ring R = 0, (%s), dp;" % ", ".join(others + [keep]), "ideal I ="]
    for k, s in enumerate(eqs):
        L.append("  %s%s" % (s, "," if k < len(eqs) - 1 else ";"))
    return "\n".join(L), keep, others

def singular(cmds):
    p = subprocess.run([SINGULAR, "-q"], input=cmds + "\nquit;\n",
                       capture_output=True, text=True, timeout=600)
    out = p.stdout + p.stderr
    if "error occurred" in out:
        raise RuntimeError("Singular error:\n" + out)
    return out

def parse_univariate(out, var):
    """Extract the E[1] = <poly> line and return {exp: coeff} with int coeffs."""
    m = re.search(r"E\[1\]=([^\n]+)", out)
    if not m:
        raise RuntimeError("no eliminant in Singular output:\n" + out)
    poly = m.group(1).replace(" ", "")
    coeffs = {}
    for term in poly.replace("-", "+-").split("+"):
        if not term:
            continue
        if var + "^" in term:
            c, e = term.split("*" + var + "^")
            coeffs[int(e)] = coeffs.get(int(e), 0) + int(c)
        elif ("*" + var) in term or term == var:
            c = term.replace("*" + var, "")
            c = int(c) if c not in ("", "-") else (1 if c == "" else -1)
            coeffs[1] = coeffs.get(1, 0) + c
        else:
            coeffs[0] = coeffs.get(0, 0) + int(term)
    return {e: c for e, c in coeffs.items() if c}

def main():
    from flint import fmpq_poly
    # paper's stated eliminants, as {exp: coeff}
    stated = {3: {3: 3, 0: -32},
              5: {10: 9, 5: 37200, 0: 95051008}}
    expected_count = {3: 3, 5: 10}
    ok = True
    for m in (3, 5):
        src, keep, others = build(m)
        vdim = int(singular(src + "\nvdim(groebner(I));\n").strip().split()[-1])
        coeffs = parse_univariate(
            singular(src + "\nideal E = eliminate(I, %s);\nE;\n" % "*".join(others)), keep)
        d = max(coeffs)
        p = fmpq_poly([coeffs.get(i, 0) for i in range(d + 1)])
        unit, facs = p.factor()
        irreducible = (len(facs) == 1 and facs[0][1] == 1 and facs[0][0].degree() == d)
        separable = p.gcd(p.derivative()).degree() == 0
        # proportional to the stated eliminant?
        st = stated[m]
        sd = max(st)
        prop = (d == sd and all(coeffs.get(i, 0) * st[sd] == st.get(i, 0) * coeffs[sd]
                               for i in range(sd + 1)))
        exact = (vdim == expected_count[m] and prop and irreducible and separable)
        print(f"m={m}: vdim={vdim} (expect {expected_count[m]}), "
              f"eliminant degree {d}, proportional to stated: {prop}, "
              f"irreducible: {irreducible}, separable: {separable} "
              f"=> EXACT count {expected_count[m]}: {exact}", flush=True)
        ok = ok and exact
    print("ALL CHECKS PASS" if ok else "CHECKS FAILED", flush=True)
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
