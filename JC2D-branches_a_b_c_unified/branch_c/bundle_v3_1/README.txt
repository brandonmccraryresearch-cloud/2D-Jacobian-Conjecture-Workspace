Branch (c) of GGHV Prop. 4.3 case (1), degree pair (72,108): bundle v3.1 (2026-09-29, 23:40 CDT)

Nothing has been pushed, committed, published, uploaded or deposited. branch_c/ is untouched. The v2
corrected-commit proposal is NOT applied. This is not a proof of the Jacobian conjecture.

START WITH GUIDE.md
  It covers the verdict, the proof chain bridge by bridge, the five steps, the correspondence with earlier results,
  the computational structures, the trust base, the controls, the HLRE claim registry, the logs index, the
  diagnostics, the open items and how to reproduce everything.

Where things stand (v3.1, verified 2026-09-29 23:36 CDT; details in GUIDE.md sections 1 and 13)
  - Lean, all modules built, `verify_branch_c_lean.sh` passes, only the standard axioms (53 theorems audited):
      ChartEmptyC_T1ne0 -> ChartEmptyC -> DescentClaimC -> no (P, Q, lambda) with [P,Q] = lambda x^2
      and the branch-(c) Newton normal form.
    The stratum b_{11,20} = 0 is kernel-checked (T1Zero); its five negative controls are all rejected.
  - Outside Lean, grade B: ChartEmptyC holds. It follows from the rank lemma plus the full row rank of the W = 24
    Macaulay matrix mod 1000003 and mod 32003, found with FLINT and confirmed by an independent numpy elimination,
    with controls. See jacobian_lean/chart_certificates/STEP3_4_CHART.md.

Layout
  GUIDE.md          the comprehensive guide
  jacobian_lean/    Lean overlay for the repository's branch-(a,b) project (Lean 4.34.0, Mathlib v4.34.0)
                      Jacobian/BranchC/**   v1/v2 modules + CondsC + Descent2R (505 + Bridge) + T1Zero (17 + Combine)
                      certgen_c/            generators and exact data (python-flint)
                      chart_certificates/   steps 1, 3, 4 outside Lean; padic_DEFERRED/ (not reviewed further)
                      BRANCH_C_LEAN_STATUS.md (v3), BRANCH_C_LEAN_STATUS.v2.md, AxiomsAuditBranchC.lean,
                      verify_branch_c_lean.sh, build_branch_c_lowmem.sh, lighten_ab_descent_imports.py
  logs/             every log (index: GUIDE.md section 9)
  diag/             procmon.py (developer-level process diagnostics), guardrun.py, leanprof.sh,
                    t1z_controls.py (five negative controls for T1Zero)
  profiling/        Lean profiler findings and their test files
  muse_refutation/  the Muse char0_cert bundle's reduction_lemma axiom proves False (review deferred)
  v2_carryover/     v2's branch_c_audit/, corrected_commit_proposal/ (NOT applied), controls/, checks/
