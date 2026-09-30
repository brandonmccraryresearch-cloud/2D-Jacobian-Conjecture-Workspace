# Branch (c) Elimination — unified package

Elimination of GGHV normal form (1) [branch (c)] in the degree-(72,108) case of the
two-dimensional Jacobian conjecture.

This package follows the format of the branch-(a,b) elimination paper package
(`../branches_a_b/`, i.e. `branch_ab`, the v19 package) exactly, with the branch-(c) elimination
worked out **symbolically** (Lean 4 formalization) and **numerically** (exact and
modular certificates, finite-field rank computations).

## Format map (branch_ab [v19]  ->  branch (c))

| branch-(a,b) component | branch-(c) location | Notes |
|---|---|---|
| `paper/` (.tex/.pdf) | `paper/BRANCH_C_GUIDE.md` | The comprehensive v3.1 guide is the paper-equivalent document. No `.tex` paper exists yet for branch (c). |
| `scripts/` | `bundle_v3_1/jacobian_lean/certgen_c/`, `bundle_v3_1/jacobian_lean/chart_certificates/` | Generators (exact, python-flint) and certificate/rank scripts. Kept inside `jacobian_lean/` because `verify_branch_c_lean.sh` requires `certgen_c/`, `chart_certificates/` and `Jacobian/` as siblings. |
| `lean/` | `bundle_v3_1/jacobian_lean/Jacobian/BranchC/` | v1/v2 modules, `Descent2R` (505 generated modules), `T1Zero`, `Combine`, `Bridge`, `CondsC` |
| `audits/` | `bundle_v3_1/jacobian_lean/axioms_branch_c.log`, `bundle_v3_1/v2_carryover/branch_c_audit/` | Axiom audit (53 theorems) + v2 audit carryover |
| `correspondence_guide/` | **deferred** | See `../TODO_correspondence_guide.md`: created only after the finalized paper is drafted. |
| `figures/` | (none) | No figures produced for branch (c) yet. |
| `logs/` | `bundle_v3_1/logs/` | Every build / verify / control / diagnostics log (index: GUIDE.md §9) |
| `BUILD_STATUS.md` | `BUILD_STATUS.md` | Full build and verification record |
| `CHECKSUMS.md5` / `CHECKSUMS.sha256` | `CHECKSUMS.md5` / `CHECKSUMS.sha256` | Generated over this `branch_c/` tree |
| `verify_v19.sh` | `verify_branch_c.sh` | Wrapper delegating to `bundle_v3_1/jacobian_lean/verify_branch_c_lean.sh` |

## The v3.1 bundle, preserved intact

`bundle_v3_1/` is the reviewer's v3.1 bundle **byte-for-byte** (verified against its
`MANIFEST.sha256` at assembly time): the Lean overlay, all generators and data, every
log, the diagnostics, the `muse_refutation/` note, and the `v2_carryover/`. It is kept
intact because `verify_branch_c_lean.sh` depends on the internal relative layout
(`certgen_c/`, `chart_certificates/`, `Jacobian/` as siblings under `jacobian_lean/`).

## Verdict (v3.1, 2026-09-29)

- In Lean (no `sorry`, only `propext`, `Classical.choice`, `Quot.sound`):
  `ChartEmptyC_T1ne0 → ChartEmptyC → DescentClaimC → ¬∃ P Q λ, λ ≠ 0 ∧ NewtonNFc P Q ∧ [P,Q] = λx²`.
  The stratum b_{11,20} = 0 is kernel-checked (`T1Zero`); `Combine` isolates exactly
  what Lean does not check.
- Outside Lean (grade B): `ChartEmptyC` follows from the rank lemma plus full row rank
  of the W = 24 Macaulay matrix mod 1000003 and mod 32003 (two implementations, controls).
- Branch (c) is therefore closed **under stated computational premises not machine-checked
  in Lean**. It is not closed by Lean alone. See `GUIDE.md` §1 for the full verdict.

## Reproduction

```bash
cd branch_c
bash verify_branch_c.sh   # delegates to bundle_v3_1/jacobian_lean/verify_branch_c_lean.sh
```

Requirements: elan/lake (Lean 4.34.0, Mathlib v4.34.0), python3 with python-flint and sympy.
Single modules peak at ~5.6 GB RSS; allow 12+ GB or set LOWMEM=1.

## Scope

Not the Jacobian conjecture, not any other case of GGHV Prop. 4.3, not the reduction
from the conjecture to Prop. 4.3. Nothing here has been published, uploaded, deposited
or minted.
