"""check_explicit_data.py -- machine check of B26_EXPLICIT_DATA.md (CAIC, 2026-10-05) against the repository.
Needs Singular (4.3.2) and Python 3 with sympy; a few seconds; run from anywhere.

1. r0..r3 in the file equal the residuals of m5_b2_6_eliminate_basis.sing and the Lean definitions m5r0..m5r3
   (lean/Jacobian/B26/Defs.lean).
2. G1..G10 in the file equal, element by element, Singular's std(S) in QQ[a1,a2,a3,a4] with ordering dp and default
   options (a Groebner basis, not the reduced one). (G1..G10) = (r0..r3) as ideals, vdim = 10, and the elimination
   ideal (r0..r3) cap Q[a4] is (T).
3. In the reduced basis (option(redSB)), the elements that are linear in (a1, a2, a3) over Q[a4] form a 3x3 system
   with determinant 30408*a4^3; T(0) != 0; the back-substitution formulas annihilate G1..G10 and r0..r3 modulo T;
   the two discriminants in the file's correction note are right.
Control: the element-by-element and membership checks of step 2 are rerun with one coefficient of G10 changed; they
must fail."""
import os, re, subprocess, sys, tempfile
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
BAB = os.path.normpath(os.path.join(HERE, "..", ".."))
md = open(os.path.join(HERE, "B26_EXPLICIT_DATA.md")).read()
sing_src = open(os.path.join(HERE, "m5_b2_6_eliminate_basis.sing")).read()
defs = open(os.path.join(BAB, "lean", "Jacobian", "B26", "Defs.lean")).read()
a1, a2, a3, a4 = A = sp.symbols("a1 a2 a3 a4")
loc = {str(v): v for v in A}
P = lambda s: sp.sympify(s.replace("^", "**").replace("\n", " "), locals=loc)
results = []


def check(name, ok):
    results.append(ok)
    print(f"{'PASS' if ok else 'FAIL'}  {name}")


file_r = dict(re.findall(r"^(r[0-3]) = (.*)$", md, re.M))
file_G = [g for _, g in sorted(((int(k), v) for k, v in re.findall(r"^G(\d+) = (.*)$", md, re.M)))]
rep_r = dict(re.findall(r"^poly (r[0-3]) = (.*);$", sing_src, re.M))
lean_r = {f"r{k}": re.search(rf"def m5r{k} \(a1 a2 a3 a4 : L\) : L :=\n(.*?)\n\n", defs, re.S).group(1)
          for k in range(4)}

# 1. residuals
for k in ("r0", "r1", "r2", "r3"):
    check(f"{k}: file == m5_b2_6_eliminate_basis.sing == Lean m5{k}",
          sp.expand(P(file_r[k]) - P(rep_r[k])) == 0 and sp.expand(P(file_r[k]) - P(lean_r[k])) == 0)
check("the file lists G1..G10", len(file_G) == 10)


# 2. Groebner basis (Singular)
def singular(G):
    script = "\n".join([
        "ring R = 0, (a1,a2,a3,a4), dp;",
        "ideal S = " + ", ".join(file_r[k] for k in ("r0", "r1", "r2", "r3")) + ";",
        "ideal Gf = " + ",\n".join(G) + ";",
        "ideal G = std(S);",
        "int same = (size(G) == size(Gf)); int i;",
        "for (i = 1; i <= size(Gf); i++) { if (i <= size(G)) { if (G[i] != Gf[i]) { same = 0; } } }",
        'print("SAME " + string(same));',
        'print("IN_S " + string(size(reduce(Gf, G)) == 0));',
        'print("GENERATES " + string(size(reduce(S, std(Gf))) == 0));',
        'print("VDIM " + string(vdim(G)));',
        "ideal E = std(eliminate(S, a1*a2*a3));",
        "ideal T = std(ideal(9*a4^10 + 37200*a4^5 + 95051008));",
        'print("ELIM_T " + string(size(E) == 1 && size(reduce(E, T)) == 0 && size(reduce(T, E)) == 0));',
        "option(redSB); ideal Gr = std(S);",
        'for (i = 1; i <= size(Gr); i++) { print("RED " + string(Gr[i])); }',
        "quit;"])
    with tempfile.NamedTemporaryFile("w", suffix=".sing", delete=False) as fh:
        fh.write(script)
    out = subprocess.run(["Singular", "-q", fh.name], capture_output=True, text=True, stdin=subprocess.DEVNULL,
                         timeout=600).stdout
    os.unlink(fh.name)
    kv = dict(l.split(" ", 1) for l in out.splitlines() if l.split(" ")[0] in ("SAME", "IN_S", "GENERATES", "VDIM",
                                                                            "ELIM_T"))
    red = [l[4:] for l in out.splitlines() if l.startswith("RED ")]
    return kv, red


kv, red = singular(file_G)
check("G1..G10 == Singular std(S) element by element (dp, default options)", kv.get("SAME") == "1")
check("each G_i lies in (r0..r3)", kv.get("IN_S") == "1")
check("(G1..G10) contains r0..r3, so the ideals are equal", kv.get("GENERATES") == "1")
check("vdim = 10", kv.get("VDIM") == "10")
check("elimination ideal (r0..r3) cap Q[a4] == (T)", kv.get("ELIM_T") == "1")

# control: one coefficient of G10 changed
bad = file_G[:9] + [file_G[9].replace("104013356", "104013357", 1)]
kvb, _ = singular(bad)
check("control (G10 coefficient 104013356 -> 104013357) is rejected",
      bad[9] != file_G[9] and kvb.get("SAME") == "0" and kvb.get("IN_S") == "0")

# 3. linear system, back-substitution, discriminants
red_p = [P(g) for g in red]
lin = [g for g in red_p if sp.Poly(g, a1, a2, a3).total_degree() <= 1]
M = sp.Matrix([[sp.Poly(g, a1, a2, a3).coeff_monomial(v) for v in (a1, a2, a3)] for g in lin])
print("      reduced-basis elements linear in (a1,a2,a3):", [str(g) for g in lin])
check("they are 3, with det = 30408*a4^3", len(lin) == 3 and sp.factor(M.det()) == 30408 * a4**3)
T = 9 * a4**10 + 37200 * a4**5 + 95051008
check("T(0) = 95051008 != 0", T.subs(a4, 0) == 95051008)
sub = {a1: (3 * a4**5 + 13078) / (362 * a4), a2: 3 * (5 * a4**5 + 10816) / (181 * a4**2),
       a3: 7 * (123 * a4**5 + 70304) / (2172 * a4**3)}
TP = sp.Poly(T, a4)


def vanishes_mod_T(f):
    num = sp.together(sp.expand(P(f).subs(sub))).as_numer_denom()[0]      # denominator is c*a4^k, a unit mod T
    return sp.Poly(num, a4).rem(TP).is_zero


check("back-substitution annihilates G1..G10 and r0..r3 modulo T",
      all(vanishes_mod_T(g) for g in file_G + [file_r[k] for k in ("r0", "r1", "r2", "r3")]))
u = sp.Symbol("u")
check("disc_u(9u^2 + 37200u + 95051008) = -2^8*3^5*181^2 = -2037996288",
      sp.discriminant(9 * u**2 + 37200 * u + 95051008, u) == -2**8 * 3**5 * 181**2 == -2037996288)
dT = sp.discriminant(T, a4)
check("disc(T) = -2^72*3^33*5^10*13^20*181^10 (90 digits)",
      dT == -2**72 * 3**33 * 5**10 * 13**20 * 181**10 and len(str(abs(dT))) == 90)
print("ALL CHECKS PASSED" if all(results) else "SOMETHING FAILED")
sys.exit(0 if all(results) else 1)
