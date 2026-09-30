"""make_patches.py -- build two proposed patches against branch_c/scripts at commit 18c9945 (not applied to the repo).

  paths/ : every hard-coded /home/hatch path becomes an environment override whose default is the original
           path (BRANCH_C_CERTGEN, BRANCH_C_WORKDIR, SINGULAR).  Behaviour on the original machine is unchanged.
  fixed/ : paths/ + the E1 projection fix: where solve_aug(M1, rhs) fails (rhs outside col(M1), i.e. the
           monomial carries Omega), project rhs along e_j0 with the left null vector W1 of M1 and solve, instead of
           `continue`.  Stage 6 has the same skip at E0 (Psi monomials) and gets the same fix with the left null
           vector of M0.  On Omega = 0 (resp. Psi = 0) the projected right-hand sides add up to the true one, so the
           particular solution solves the layer equations there; the old `continue` dropped the solvable part.
"""
import os, re, shutil, sys
HERE = os.path.dirname(os.path.abspath(__file__))
# usage: python3 make_patches.py [path/to/branch_c/scripts at commit 18c9945]   (default: reuse ./orig/)
SRC = sys.argv[1] if len(sys.argv) > 1 else None
ORIG, PATHS, FIXED = (os.path.join(HERE, d) for d in ("orig", "paths", "fixed"))
if SRC:
    shutil.rmtree(ORIG, ignore_errors=True); os.makedirs(ORIG)
    for f in os.listdir(SRC):
        if f.endswith(".py"): shutil.copy(os.path.join(SRC, f), os.path.join(ORIG, f))
for d in (PATHS, FIXED):
    shutil.rmtree(d, ignore_errors=True); os.makedirs(d)
files = sorted(f for f in os.listdir(ORIG) if f.endswith(".py"))
assert len(files) == 10, files

CONFIG = [
    'import os as _os, shutil as _shutil  # configurable paths (defaults = the original machine)',
    'CERTGEN = _os.environ.get("BRANCH_C_CERTGEN", "/home/hatch/workspace/v18/branch_ab_v19/lean/certgen")',
    'WORKDIR = _os.environ.get("BRANCH_C_WORKDIR", "/home/hatch/workspace")',
    'SINGULAR = _os.environ.get("SINGULAR", "/home/hatch/miniconda3/envs/cas/bin/Singular")',
    'if "SINGULAR" not in _os.environ and not _os.path.exists(SINGULAR): SINGULAR = _shutil.which("Singular") or SINGULAR',
]
REPL = [
    ('f"/home/hatch/workspace/stage6e_prong2_k{ki}.sing"', '_os.path.join(WORKDIR, f"stage6e_prong2_k{ki}.sing")'),
    ('"/home/hatch/workspace/v18/branch_ab_v19/lean/certgen/e5_exact_K5.json"', '_os.path.join(CERTGEN, "e5_exact_K5.json")'),
    ('"/home/hatch/workspace/v18/branch_ab_v19/lean/certgen"', 'CERTGEN'),
    ('"/home/hatch/miniconda3/envs/cas/bin/Singular"', 'SINGULAR'),
    ('"/home/hatch/workspace/stage6d_prong1.sing"', '_os.path.join(WORKDIR, "stage6d_prong1.sing")'),
    ('"/home/hatch/workspace/stage6d_prong2.sing"', '_os.path.join(WORKDIR, "stage6d_prong2.sing")'),
    ('"/home/hatch/workspace/stage6_phi.pkl"', '_os.path.join(WORKDIR, "stage6_phi.pkl")'),
    ('sing_dir="/home/hatch/workspace"', 'sing_dir=WORKDIR'),
    # Singular reads further commands from stdin after the .sing file (which has no `quit;`); with an inherited
    # terminal, pipe or socket it waits until the timeout.  stdin=DEVNULL makes it exit.  Output is unchanged.
    ('capture_output=True,text=True,timeout=', 'capture_output=True,text=True,stdin=subprocess.DEVNULL,timeout='),
]
for f in files:
    lines = open(os.path.join(ORIG, f)).read().split("\n")
    idx = next((i for i, l in enumerate(lines) if "/home/hatch" in l), None)
    if idx is not None:
        body = "\n".join(lines[idx:])
        for a, b in REPL: body = body.replace(a, b)
        assert "/home/hatch" not in body, (f, [l for l in body.split("\n") if "/home/hatch" in l])
        lines = lines[:idx] + CONFIG + body.split("\n")
    open(os.path.join(PATHS, f), "w").write("\n".join(lines))

def helper(name, M, tag):
    return [
        f"# E{tag} compatibility (fix): {M} has a one-dimensional left null space.  A right-hand side outside col({M})",
        f"# has W.rhs equal to its coefficient in the E{tag} obstruction; the old `continue` dropped such monomials",
        f"# entirely, so the particular solution did not solve E{tag} even where the obstruction vanishes.  Project",
        f"# along e_j0 instead: where the obstruction vanishes, the projected right-hand sides add up to the true one.",
        f"_MT{name}=[[{M}[r][c] for r in range(len({M}))] for c in range(len({M}[0]))]",
        f"_N{name}=nullspace(_MT{name},len({M}))[0]; assert len(_N{name})==1, 'left null space of {M} is not 1-dimensional'",
        f"_W{name}=_N{name}[0]",
        f"_j{name}=next(j for j in range(len(_W{name})) if _W{name}[j]!=ZERO)",
        f"def _proj_{name}(rhs):",
        f"    wr=ZERO",
        f"    for j in range(len(_W{name})): wr=(wr+_W{name}[j]*rhs[j])%Rr",
        f"    return [(rhs[j]-(wr*kinv(_W{name}[_j{name}]) if j==_j{name} else ZERO))%Rr for j in range(len(rhs))]",
    ]
EDITS = {  # file: list of (loop header, old skip text, new text, helper args)
    "branch_c_stage5_e0_compatibility.py": [("for m in monos1:",
        '    if sol is None:\n        print(f"  E_1 unsolvable for monomial {m} (expected iff Omega!=0)")\n        continue',
        '    if sol is None:\n        print(f"  E_1: monomial {m} carries Omega; W1-component projected out (valid on Omega = 0)")\n'
        '        sol=solve_aug(M1,_proj_E1(rhs)); assert sol is not None', ("E1", "M1", "1"))],
    "branch_c_stage6_e_minus1_obstruction.py": [
        ("for m in monos1:", "    if sol is None: continue  # Omega monomials",
         "    if sol is None: sol=solve_aug(M1,_proj_E1(rhs)); assert sol is not None  # Omega monomials: projected",
         ("E1", "M1", "1")),
        ("for m in monos0:", "    if sol is None:\n        n_unsolv+=1; continue  # Psi != 0",
         "    if sol is None:\n        n_unsolv+=1; sol=solve_aug(M0,_proj_E0(rhs)); assert sol is not None  # Psi monomials: projected",
         ("E0", "M0", "0"))],
    # (the E0 count line is re-worded below, in FIXED only)
    "branch_c_stage6b_phi12.py": [("for m in monos1:", "    if sol is None: continue",
        "    if sol is None: sol=solve_aug(M1,_proj_E1(rhs)); assert sol is not None", ("E1", "M1", "1"))],
    "branch_c_stage6c_e_minus2.py": [("for m in monos1:", "    if sol is None: continue",
        "    if sol is None: sol=solve_aug(M1,_proj_E1(rhs)); assert sol is not None", ("E1", "M1", "1"))],
    "branch_c_stage6d_weighted_sieve.py": [("for m in monos1:", "    if sol is None:continue",
        "    if sol is None:sol=solve_aug(M1,_proj_E1(rhs));assert sol is not None", ("E1", "M1", "1"))],
    "branch_c_stage6e_patch101.py": [("for m in monos1:", "    if sol is None:continue",
        "    if sol is None:sol=solve_aug(M1,_proj_E1(rhs));assert sol is not None", ("E1", "M1", "1"))],
}
for f in files:
    s = open(os.path.join(PATHS, f)).read()
    for loop, old, new, (name, M, tag) in EDITS.get(f, []):
        assert s.count(loop) == 1, (f, loop, s.count(loop))
        i = s.index(loop)
        seg_end = s.index("\n", s.index(old, i))  # the skip must follow its loop header
        assert s.count(old) == 1 and s.index(old) > i, (f, old)
        s = s[:i] + "\n".join(helper(name, M, tag)) + "\n" + s[i:]
        s = s.replace(old, new)
    if f == "branch_c_stage6_e_minus1_obstruction.py":
        old = 'print(f"E_0 solved. Unsolvable monomials (Psi!=0): {n_unsolv} / {len(monos0)}")'
        assert s.count(old) == 1
        s = s.replace(old, 'print(f"E_0 solved. Psi-carrying monomials projected (valid where Omega = Psi = 0): {n_unsolv} / {len(monos0)}")')
    open(os.path.join(FIXED, f), "w").write(s)
print("patched:", sorted(EDITS))

# final/ : fixed/ + the stage-6d kappa fix.  Stage 6d keys Omega by 7-tuples (t1,t2,s1,s2,r1,r2,q) but looked up
# c1, c2, c3 with 6-tuples, so c1 = c2 = c3 = 0, kappa = 0, and its Prong 2 ran on {t1 = 1, s2 = 0} instead of
# {t1 = 1, s2 = kappa t2^2}; its own check printed "Omega substituted terms (should be 0): 1".  Stage 6e (the
# README's Prong 2) already uses 7-tuples; this makes 6d agree with it and turns both checks into assertions.
FINAL = os.path.join(HERE, "final")
shutil.rmtree(FINAL, ignore_errors=True); os.makedirs(FINAL)
KAPPA = {"branch_c_stage6d_weighted_sieve.py": [
    ("c1=to_mod(Omega.get((0,0,0,2,0,0),ZERO))", "c1=to_mod(Omega.get((0,0,0,2,0,0,0),ZERO))"),
    ("c2=to_mod(Omega.get((0,2,0,1,0,0),ZERO))", "c2=to_mod(Omega.get((0,2,0,1,0,0,0),ZERO))"),
    ("c3=to_mod(Omega.get((0,4,0,0,0,0),ZERO))", "c3=to_mod(Omega.get((0,4,0,0,0,0,0),ZERO))\n"
     "assert not (c1==0 and c2==0 and c3==0), \"Omega degenerate mod p (wrong keys?)\""),
    ('    print(f"  Omega substituted terms (should be 0): {len(om_sub)}")',
     '    print(f"  Omega substituted terms (should be 0): {len(om_sub)}")\n    assert len(om_sub)==0, "kappa is not a root of Omega"'),
    ("    print(r2.stdout[:1500])",
     "    print(r2.stdout[:1500])\n    print(f\"  G = <1>: {r2.stdout.strip().split(chr(10))[0].replace(' ','')=='G[1]=1'}\")"),
],
"branch_c_stage6e_patch101.py": [
    ('    if "1" in out.split():\n        # check if G[1]=1 or similar\n        print("  *** CONTAINS 1? Check manually ***")',
     "    # (the old test `\"1\" in out.split()` never fired: the output token is \"G[1]=1\")\n"
     "    print(f\"  G = <1>: {out.split(chr(10))[0].replace(' ','')=='G[1]=1'}\")"),
]}
for f in files:
    s = open(os.path.join(FIXED, f)).read()
    for old, new in KAPPA.get(f, []):
        assert s.count(old) == 1, (f, old)
        s = s.replace(old, new)
    open(os.path.join(FINAL, f), "w").write(s)
print("checks fix:", sorted(KAPPA))
