Branch (c) Lean 4 formalization bundle, v2 (GGHV Prop 4.3 case (1), degree pair (72,108)).
Nothing has been pushed, committed, published or deposited. The repository's branch_c/ is untouched.
This is not a proof of the Jacobian conjecture: only the branch-(c) elimination steps are formalized, and the
characteristic-0 Groebner step is an open item (jacobian_lean/BRANCH_C_LEAN_STATUS.md, sections 3-4).

jacobian_lean/   Overlay for the root of the branch-(a,b) Lean project (Lean 4.34.0 / Mathlib v4.34.0,
                 e.g. <repo>/branch_ab_v17/lean):
                   Jacobian/BranchC/**              162 Lean sources (hand-written + generated); no sorry/axiom
                   certgen_c/                       generators and exact certificate data (python-flint)
                   AxiomsAuditBranchC.lean          #print axioms on 41 theorems (log: axioms_branch_c.log)
                   verify_branch_c_lean.sh          prerequisites -> regenerate+diff -> build -> axioms -> grep
                   build_branch_c_lowmem.sh         one-module-at-a-time build for machines under ~12 GB (NEW)
                   lighten_ab_descent_imports.py    optional: E3 modules 5.0 -> 2.7 GB, MainOmega 5.2 -> 2.2 GB (NEW)
                   BRANCH_C_LEAN_STATUS.md          status, ledger, evidence, findings, memory table, v2 notes
                 On a 7 GB machine:  python3 lighten_ab_descent_imports.py && LOWMEM=1 ./verify_branch_c_lean.sh
corrected_commit_proposal/
                 Proposed fix of the committed branch_c/ scripts (commit 18c9945): four patches, tested, NOT
                 APPLIED. See its README.md. Applying, committing or pushing needs Brandon's explicit word.
branch_c_audit/  The audit scripts (portable: BRANCH_C_CERTGEN, SINGULAR), their inputs and outputs, and the logs.
                 See README_audit.md. It was reproduced byte for byte from a clean copy.
controls/        Negative controls (Lean) for the new lemmas.
checks/          Small Python cross-checks.

Changes since v1:
 - verify_branch_c_lean.sh
     New step 0 checks that the branch-(a,b) prerequisites are the repository's: certgen inputs
     442bf8d1f27248f0, and the 54 Descent E4/E3red/E3 files 260a235be1028994 with import lines ignored, so
     repository trees (v17/v19, `import Mathlib`) and lightened trees both match.
     A missing file or a one-character change in a proof fails it.
     Step 2 builds one module at a time below 12 GB of free memory.
 - Sequential build script with per-module time and peak memory, and a `--no-build` fast path.
 - Memory table (RSS and heap) that explains the failed parallel build on 7 GB.
 - lower_c.py
     Singular is taken from $SINGULAR or PATH.
     Its "Omega at s2 = kappa t2^2 vanishes: True" line was a mislabelled check: it tested only that the
     coefficients reduce mod 101. It is now an exact K5 check with a control. The statement holds, and it is
     also proved in Lean (OmegaSquare + OmegaEdge).
 - New findings in branch_c/, each fixed in the proposal:
   * stage 6d computes kappa = 0 (6-tuple vs 7-tuple keys), so its Prong 2 ran on the wrong locus. No committed
     result depends on it, because the README's Prong 2 is 6e. After patch 03, 6d gives <1> at a second prime,
     p = 1000003.
   * stage 6 skipped all 32 E0 monomials, so its E0 solution was 0 and it printed a 56-term Phi.
     Patch 02 includes an exact K5 cross-check with a negative control.
   * Singular inherits stdin and the .sing files have no quit;, so the scripts hang when stdin is a terminal,
     pipe or socket (observed).
   * 6e's test for <1> can never fire.
   * verify_branch_c.sh never asserted G[1]=1.
 - branch_c_audit
     The copies of the stage scripts are removed; use corrected_commit_proposal/paths (the committed logic,
     portable) or final (corrected).
     The audit scripts no longer contain machine paths.
