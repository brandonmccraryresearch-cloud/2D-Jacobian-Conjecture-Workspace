# JC2D Branches (a), (b), (c) — Unified

Elimination of the degree-(72,108) candidate of GGHV Proposition 4.3, case (1),
for the two-dimensional Jacobian conjecture: branches (a), (b) and (c), organized
in one directory.

| Directory | Branch | Elimination paper package |
|---|---|---|
| `branches_a_b/` | (a), (b) — GGHV normal form (2), degree-(8,28) case | The v19 package, revised 2026-10-05 to 2026-10-07; the identical copy `branch_ab_v19/` at the repository root is the path the Zenodo record cites. Contents: a 34-page paper, a Lean 4 machine-checked m = 7 chart classification (Prop. 6.1), Lean m = 3, 5 classifications, the Lean proof of Corollary 1.2 (a₈,₁₆ = 0, lower-edge rigidity), four certificates, the explicit a₈,₁₆ certificate, audits, logs, `verify_v19.sh` |
| `branch_c/` | (c) — GGHV normal form (1), degree-(72,108) case | v3.1 bundle in the branch-(a,b) paper format: symbolic elimination in Lean 4 (`Descent2R`, `T1Zero`, `Bridge`, `Combine`) + numerical elimination (exact/modular certificates, rank lemma), `verify_branch_c.sh` |

## Reading order

1. `TECHNICAL_MAP.md` — the exhaustive technical map: the mathematics, every
   component, the symbolic and numerical eliminations branch by branch, the trust
   base, and how to reproduce everything.
2. `branches_a_b/README.md` — the branch-(a,b) elimination (v19).
3. `branch_c/README.md` then `branch_c/GUIDE.md` — the branch-(c) elimination (v3.1).

## Status

- Branches (a,b): eliminated. Lean proves `main_theorem` (no remaining hypothesis)
  on the standard axioms; the paper is finalized through v19 (Zenodo 10.5281/zenodo.23023490).
- Branch (c): closed **under stated computational premises not machine-checked in Lean**
  (v3.1 verdict, GUIDE.md §1). In Lean, with no `sorry` and only the standard axioms:
  `ChartEmptyC_T1ne0 → ChartEmptyC → DescentClaimC → ¬∃ P Q λ, λ ≠ 0 ∧ NewtonNFc P Q ∧ [P,Q] = λx²`.
  Outside Lean (grade B): `ChartEmptyC` via the rank lemma + finite-field ranks at two primes.
  Since 2026-10-06, `branch_c/rank_lemma_check/` checks the premises: R is irreducible, and the generators are
  exactly the Lean conditions. The Lean kernel also checks the arithmetic, through an explicit inverse of the pivot
  block. The grade stays B, because the link from that arithmetic to `ChartEmptyC_T1ne0` is not in Lean.
- Neither branch resolves the Jacobian conjecture; GGHV Prop. 4.3's other cases and the
  reduction to it are outside scope.

## Deferred

- `TODO_correspondence_guide.md` — the branch-(c) correspondence guide is created
  **only after** the finalized paper is drafted (conditional to-do, not started).
- Branch (c), grade A for `ChartEmptyC_T1ne0` (plan A1–A5, about 9–15 sessions): deferred by decision on 2026-10-06.
  The outside replication (I3) is specified in `branch_c/rank_lemma_check/I3_REPLICATION_SPEC.md` and is still open.
  See `TECHNICAL_MAP.md` §9.
- Closed on 2026-10-06:
  - the p-adic argument (not needed);
  - the Muse `char0_cert` bundle (withdrawn, superseded by v3; `branch_c/muse_refutation/`).
