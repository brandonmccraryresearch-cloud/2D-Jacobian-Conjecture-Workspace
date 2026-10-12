"""
check_logs.py -- compare the outputs of the answer key's Singular and PARI/GP scripts with ANSWER_KEY.md.

DO NOT READ OR RUN THIS BEFORE YOU HAVE RECORDED YOUR OWN RESULTS (see ../INDEPENDENT_REPLICATION_GUIDE.md).

Each expectation is a header line of the log followed by the lines expected right after it (exact match after
stripping blanks). Prints one line per expectation; the last line is "LOG CHECKS: n passed, m failed".
Run after run_key.sh (or after the individual scripts): python3 check_logs.py
"""
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
EXPECT = {
    "field.log": [
        ("R irreducible over Q: 1", []),
        ("polredabs(R) == R: 1", []),
        ("V irreducible: 1   polredabs(V) == R: 1", []),
        ("V(t^7) irreducible (degree 35): 1", []),
        ("real roots: R 1, V 1, V(t^7) 1", []),
        ("field discriminant: 3065712 = [2, 4; 3, 1; 13, 1; 17, 3]", []),
        ("signature (r1, r2): [1, 2]", []),
        ('Galois group of R: [120, -1, 1, "S5"]', []),
        ("class number: 1", []),
    ],
    "top_layer_counts.log": [
        ("chart alpha0=beta0=alpha7=1 (mod 32003): dim", ["0", "vdim", "35", "deg of eliminant in a6:", "35"]),
        ("chart alpha0=beta0=alpha1=1 with alpha7 != 0 (mod 32003): dim", ["0", "vdim", "5"]),
        ("radical check: vdim of radical", ["5"]),
    ],
    "top_layer_m35.log": [
        ("m = 3: equations", ["2", "dim", "0", "vdim (solutions with multiplicity)", "3",
                              "eliminant in alpha_2 (monic):", "a(2)^3-32/3"]),
        ("factorization over Q:", ["[1]:", "_[1]=1", "_[2]=3*a(2)^3-32", "[2]:", "1,1",
                                   "vdim of the radical (distinct solutions):", "3"]),
        ("m = 5: equations", ["4", "dim", "0", "vdim (solutions with multiplicity)", "10",
                              "eliminant in alpha_4 (monic):", "a(4)^10+12400/3*a(4)^5+95051008/9"]),
        ("factorization over Q:", ["[1]:", "_[1]=1", "_[2]=9*a(4)^10+37200*a(4)^5+95051008", "[2]:", "1,1",
                                   "vdim of the radical (distinct solutions):", "10"]),
    ],
    "descent_ideal.log": [
        ("E4,E3,E2 equations:", ["56", "E4..E1 equations:", "75"]),
        ("[R5] dim of V(E4,E3,E2) in the 51 unknowns (Singular dim minus the 5 free ring variables a_0_0, b_0_0, z, x, y):", ["2"]),
        ("[R5] b_12_24 in the radical of I(E4,E3,E2):", ["1"]),
        ("[R5] b_12_24 in I(E4,E3,E2) itself:", ["0"]),
        ("[R5] t1 = b_11_20 and t2 = b_12_22 in the radical:", ["1", "1"]),
        ("[R5] t1^3 in I: 0   t2^3 in I: 0", ["[R5] t1^4 in I: 1   t2^4 in I: 1"]),
        ("[R5] elimination ideal I(E4,E3,E2) cap K5[t1,t2]: degrees of its reduced Groebner basis (degree ordering)",
         ["3", "3", "4", "4"]),
        ("[R5] the elimination ideal is homogeneous in (t1, t2) (1 = yes):", ["1"]),
        ("[R5] length of K5[t1,t2]/(I cap K5[t1,t2]):", ["8"]),
        ("[R5] its Hilbert function in degrees 0..5:", ["1,2,3,2,0,0"]),
        ("[R5] degrees of a minimal generating set of I cap K5[t1,t2]:", ["3", "3", "4"]),
        ("[R6] dim of V(E4,...,E1) in the 51 unknowns:", ["0"]),
        ("[R6] a_8_16 in I(E4..E1):", ["0"]),
        ("[R6] a_8_16^2 in I(E4..E1):", ["1"]),
        ("[R6] b_12_24 in I(E4..E1):", ["0"]),
    ],
}
ok = [0, 0]
for log, items in EXPECT.items():
    lines = [l.strip() for l in open(os.path.join(HERE, "logs", log)).read().split("\n")]
    pos = 0
    for head, after in items:
        try:
            i = lines.index(head, pos)
            good = lines[i + 1:i + 1 + len(after)] == after
            pos = i + 1
        except ValueError:
            good = False
        print(("PASS  " if good else "FAIL  ") + f"{log}: {head[:70]}")
        ok[0 if good else 1] += 1
print(f"LOG CHECKS: {ok[0]} passed, {ok[1]} failed")
sys.exit(1 if ok[1] else 0)
