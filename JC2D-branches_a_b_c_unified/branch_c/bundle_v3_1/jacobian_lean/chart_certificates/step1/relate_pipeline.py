"""How lower_c's ideal relates to the (corrected) pipeline's: audit_fix.pkl (stage 6e with the W1 projection) and
audit_extra_fix.pkl (the pure rows).  1) termwise proportionality of the 7-variable generators; 2) if not
proportional, express each pipeline generator in lower_c's generators (exact K5 linear algebra)."""
import pickle, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lowerc_chart import *
AUD = sys.argv[1] if len(sys.argv) > 1 else os.environ.get("AUDIT_DIR", os.path.join(HERE, "..", "..", "audit_repro"))
d = pickle.load(open(os.path.join(AUD, "audit_fix.pkl"), "rb"))
x = pickle.load(open(os.path.join(AUD, "audit_extra_fix.pkl"), "rb"))
pipe = {n: {tuple(m): K(c) for m, c in P.items()} for n, P in d["polys"].items()}
pipe["Omega"] = {tuple(m): K(c) for m, c in d["Omega"].items()}
for n, P in x.items(): pipe[n] = {tuple(m): K(c) for m, c in P.items()}
C7 = load7()
pairs = [("Omega", "Omega"), ("Psi", "Psi"), ("Phi1", "Phi1"), ("Phi2", "Phi2"), ("Th1", "Theta1"), ("Th2", "Theta2"),
         ("Th3", "Theta3"), ("X0_18", "E0pure_18_37"), ("Xm1_17", "Em1pure_17_36"), ("Xm1_18", "Em1pure_18_38"),
         ("Xm2_16", "Em2pure_16_35"), ("Xm2_17", "Em2pure_17_37")]
for a, b in pairs:
    A, B = pipe[a], C7[b]
    A = {k: v for k, v in A.items() if v != 0}
    same = set(A) == set(B)
    m0 = next(iter(B)); c = (A.get(m0, Z) * kinv(B[m0])) % Rr if B[m0] != 0 else None
    prop = same and all((A[m] - c * B[m]) % Rr == 0 for m in B)
    print(f"{a:7s} vs {b:14s}: terms {len(A)}/{len(B)}, same support {same}, proportional {prop}"
          + (f", ratio is 1: {c == 1}, ratio is -1: {c == -1}" if prop else ""))
