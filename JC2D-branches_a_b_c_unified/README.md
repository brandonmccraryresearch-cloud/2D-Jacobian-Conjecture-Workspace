# JC2D Branches (a), (b), (c) — Unified

Elimination of the degree-(72,108) candidate of GGHV Proposition 4.3, case (1),
for the two-dimensional Jacobian conjecture: branches (a), (b) and (c), organized
in one directory.

| Directory | Branch | Elimination paper package |
|---|---|---|
| `branches_a_b/` | (a), (b) — GGHV normal form (2), degree-(8,28) case | `branch_ab` (exact copy of the v19 package): 31-page paper, Lean 4 machine-checked m = 7 chart classification (Prop. 6.1), four certificates, audits, logs, `verify_v19.sh` |
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
- Neither branch resolves the Jacobian conjecture; GGHV Prop. 4.3's other cases and the
  reduction to it are outside scope.

## Deferred

- `TODO_correspondence_guide.md` — the branch-(c) correspondence guide is created
  **only after** the finalized paper is drafted (conditional to-do, not started).
