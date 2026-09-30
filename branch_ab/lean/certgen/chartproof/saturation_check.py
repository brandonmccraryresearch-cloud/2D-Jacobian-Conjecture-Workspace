#!/usr/bin/env python3
"""saturation_check.py -- context for Step 2 of the proof of Theorem 6.5 (paper Section 6.4); NOT used by the
proof or by the Lean formalization.

Writes saturation_Q.sing and runs it in Singular over Q, with y_i of weight i. Let (g) be the ideal of the six
orbit relations (stage2.json "G") and (S) = (S_11, ..., S_16). The script checks:
  R1  S_11, ..., S_16 reduce to 0 modulo a Groebner basis of (g), i.e. (S) is contained in (g);
  R2  (g) : y7 = (g), i.e. y7 is a nonzerodivisor modulo (g);
  R3  Krull dim (g) = 1, so the six relations form a complete intersection in 7 variables, and a minimal
      generating set of (g) has 6 elements, of weights 4, 5, 5, 6, 6, 7;
  R4  the relations have exactly 5 solutions in the chart y1 = 1 (vdim = 5), as weighted Bezout predicts:
      4*5*5*6*6*7/7! = 5;
  R5  (g, y1) has Krull dimension 0, i.e. y1 = 0 forces y = 0, so all projective solutions lie in the chart.
Together with the certificates y7^3 * g in (S), R1 and R2 give (S) : y7^inf = (S) : y7^3 = (g) over Q:
(S) <= (g) <= (S) : y7^3 <= (S) : y7^inf, and f * y7^N in (S) <= (g) implies f in (g) by R2.
Usage: python3 saturation_check.py   (needs Singular on PATH; runs in a few seconds)
"""
import json, os, re, subprocess, sys
import sympy as sp
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from yform import S_list, Y

def sing(p):
    """Singular syntax with explicit (p/q)* coefficients (Singular would parse y^2/3 as y^(2/3))."""
    P = sp.Poly(sp.expand(p), *Y)
    out = []
    for mon, c in P.terms():
        c = sp.Rational(c)
        coef = f"({c.p})" if c.q == 1 else f"({c.p}/{c.q})"
        m = "*".join(f"y{i+1}^{e}" if e > 1 else f"y{i+1}" for i, e in enumerate(mon) if e > 0)
        out.append(coef + ("*" + m if m else ""))
    return " + ".join(out) if out else "0"

loc = {f'y{i}': Y[i-1] for i in range(1, 8)}
G = json.load(open(os.path.join(HERE, 'stage2.json'), encoding='utf-8'))['G']
g = [sp.sympify(G[n], locals=loc) for n in ['g4', 'g5a', 'g5b', 'g6a', 'g6b', 'g7']]
S = S_list(16)
script = '\n'.join([
    'ring r = 0,(y1,y2,y3,y4,y5,y6,y7),wp(1,2,3,4,5,6,7); option(redSB);',
    'ideal g = ' + ',\n  '.join(sing(x) for x in g) + ';',
    'ideal S = ' + ',\n  '.join(sing(S[k]) for k in range(11, 17)) + ';',
    'ideal G = std(g);',
    'int ok1 = 1; for (int k = 1; k <= 6; k++) { if (reduce(S[k], G) != 0) { ok1 = 0; } } "R1 " + string(ok1);',
    'ideal Qt = std(quotient(G, y7)); "R2 " + string(size(reduce(Qt, G)) == 0);',
    '"R3dim " + string(dim(G));',
    'ideal M = minbase(g); string wts = ""; for (int i = 1; i <= size(M); i++) { wts = wts + " " + string(deg(M[i])); }',
    '"R3gens " + string(size(M)) + " weights" + wts;',
    'ring r1 = 0,(y1,y2,y3,y4,y5,y6,y7),dp; ideal g1 = std(imap(r, g) + ideal(y1 - 1));',
    '"R4 " + string(vdim(g1));',
    'ideal g0 = std(imap(r, g) + ideal(y1)); "R5 " + string(dim(g0));',
    'quit;',
]) + '\n'
path = os.path.join(HERE, 'saturation_Q.sing')
open(path, 'w', encoding='utf-8').write(script)
res = subprocess.run(['Singular', '-q', path], capture_output=True, text=True)
out = res.stdout
print(out, end='')
if res.returncode != 0 or res.stderr.strip():
    print(res.stderr, end=''); print("FAIL: Singular error"); sys.exit(1)
get = lambda tag: (re.search(rf'^{tag} (.*)$', out, re.M) or [None, None])[1]
checks = {
    'R1 (S11..S16) in (g)': get('R1') == '1',
    'R2 (g):y7 == (g)': get('R2') == '1',
    'R3 dim (g) == 1': get('R3dim') == '1',
    'R3 minimal generators: 6, weights 4 5 5 6 6 7': (get('R3gens') or '').split() == ['6', 'weights', '4', '5', '5', '6', '6', '7']
        or sorted(map(int, (get('R3gens') or '0 weights').split()[2:])) == [4, 5, 5, 6, 6, 7] and (get('R3gens') or '').split()[0] == '6',
    'R4 vdim in chart y1 = 1 == 5': get('R4') == '5',
    'R5 dim (g, y1) == 0': get('R5') == '0',
}
for k, v in checks.items():
    print(('PASS  ' if v else 'FAIL  ') + k)
if all(checks.values()):
    print("PASS: over Q, (S11..S16) : y7^inf = (S11..S16) : y7^3 = (g), a complete intersection with 5 solutions, all with y1 != 0")
else:
    sys.exit(1)
