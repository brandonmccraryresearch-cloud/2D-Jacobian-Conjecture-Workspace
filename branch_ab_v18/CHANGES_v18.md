# v18 changes vs published v17 (commit 45dc9b3)

This tree is `branch_ab_v18/`; the published v17 tree is preserved unchanged as
`branch_ab_v17/`. Local-only v18 development. Nothing here has been pushed or published.

## 1. Proposition 6.1 — m=3, m=5 bounds proved sharp
- `branch_ab_v17/paper/branch_ab_elimination_v3.tex` (and recompiled `.pdf`)
- The proof previously stated exact counts (3, 10) for m=3, m=5 but proved only
  upper bounds. The false "only the upper bound" sentence is replaced with the
  sharpness argument: in the normalization α₀=β₀=α_m=1 the system is
  zero-dimensional of vector-space dimension 3 (m=3) / 10 (m=5); eliminating all
  variables but a_{m−1} gives the stated eliminant up to a nonzero rational
  factor; each eliminant is irreducible and separable over ℚ, so all d roots are
  realized (Galois-stable), giving exactly d solutions.
- `v18_source_changes.diff` shows the exact .tex change.

## 2. New script: exact m=3, m=5 solution counts
- `branch_ab_v17/scripts/e5_exact_counts_m35.py` (new)
- Builds the normalized E5 systems for m=3,5, runs Singular elimination and
  `vdim`, compares against the stated eliminants, and checks irreducibility and
  separability with FLINT. Verified: ALL CHECKS PASS (exit 0).
- Run: `cd lean/certgen && SINGULAR=<path>/Singular python3 ../../scripts/e5_exact_counts_m35.py`

## 3. Planted known-good E2 control in exact_obstruction_K5.py
- `branch_ab_v17/scripts/exact_obstruction_K5.py`
- The docstring promised a planted control that exercises steps 1–4; the script
  never ran one. Now implemented: shifts the E2 inhomogeneity by a constant
  vector so a planted (t0,s0,b0*) solves the E2 system, then confirms the
  machinery reports consistency — 7 conditions vanish at (t0,s0), all 35 minors
  vanish at t0, the 7×3 condition matrix drops from full rank 3 (original,
  obstructed at t0) to rank ≤ 2 (planted, consistent), and the planted E2 system
  is directly solvable with zero residual.
- Note: the planted minors are inhomogeneous (constant shift), so the
  homogeneous rank-6 span criterion is replaced by the condition-matrix rank
  comparison. Verified: exit 0.
- `v18_source_changes.diff` shows the exact change.

## 4. Promised E3 check in exact_ranks_K5.py
- `branch_ab_v17/scripts/exact_ranks_K5.py`
- The docstring promised "whether E3 is solvable for every t"; the script only
  printed ranks. Now implemented: the single left null vector of the 19×20 E3
  Jacobian kills the quadratic E3 inhomogeneity K(t) identically in t, so E3 is
  solvable for every t in characteristic 0. Verified: exit 0.
- `v18_source_changes.diff` shows the exact change.

## 5. Documentation
- `branch_ab_v17/scripts/README.md` — documents the new/changed scripts.
- `branch_ab_v17/CHECKSUMS.md5`, `CHECKSUMS.sha256` — regenerated for the
  232-file v18 bundle subset.

## Verification (from clean extraction of branch_ab_final_v18_0.zip)
- 235/235 checksums pass; all three scripts exit 0; 111/111 identities pass;
  paper PDF contains the new proof text.

## 6. Title block — source link (2026-09-28)
- `branch_ab_v18/paper/branch_ab_elimination_v3.tex` (and recompiled `.pdf`)
- The title-page "Computation, Lean and LaTeX Source:" label is now black;
  the link target is the GitHub repository
  `https://github.com/brandonmccraryresearch-cloud/2D-Jacobian-Conjecture-Workspace`
  (replacing the Google Drive link), displayed in magenta. Verified in the
  compiled PDF: label black, link magenta, link target the repo URL.
