# Branch (c) — Build Status

Source: v3.1 bundle (2026-09-29, 23:40 CDT), verified 23:28–23:36 CDT the same day.
Full record: `bundle_v3_1/jacobian_lean/BRANCH_C_LEAN_STATUS.md`; comprehensive guide: `GUIDE.md` §1.3, §13.

## Lean modules (all built, `verify_branch_c_lean.sh` passes, exit 0)

| Group | Modules | State |
|---|---|---|
| v1/v2 branch-(c) modules (`Degree19`, `LayerE2`, `LayersGen`, `Edge19`, `OmegaSquare`, `OmegaEdge`, `DescentClaim`, `Descent/**` (59), `Rank/**` (96)) | 162 | built in v2; axioms audited (`logs/axioms_branch_c.v2.log`) |
| `Descent2R/Facts`, `Vals_*`, layers L4, L3, L2c, L1, L0, Lm1, Lm2 | 505 | built (`logs/build_refl.log`: 2.9 h module time, peak 5.6 GB RSS) |
| `CondsC` | 1 | built (175 s, peak 1.78 GB) |
| `Descent2R/Main` (`chart_descent_refl`) | 1 | built: "Build completed successfully (1243 jobs)", 2,298 s, peak 3.34 GB |
| `Descent2R/Bridge` | 1 | built after a fix (269 s, no warnings) — a bug found and fixed after v3.0 |
| `T1Zero/Defs`, `Sq`, `F_*` (6), `P_*` (6), `Final` | 14 | built, 0 warnings (`P_*` 61–121 s, `Final` 46 s) |
| `T1Zero/Main` (`chartEmpty_t1_zero`) | 1 | built, 26 s |
| `T1Zero/Combine` | 1 | built, 22 s |
| Axiom audit (`AxiomsAuditBranchC.lean`) | 53 theorems | passed: 52 depend on `[propext, Classical.choice, Quot.sound]`; `Omega.omega_mod101_square` on `[propext, Quot.sound]` |
| `verify_branch_c_lean.sh` | — | passed, exit 0: prerequisite fingerprints; v2+v3 regeneration byte-identical; all 790 modules up to date; axioms; no `sorry`/`axiom`/`native_decide` |

## Outside Lean (grade B)

- `ChartEmptyC` (hence `ChartEmptyC_T1ne0`) via the rank lemma + full row rank of the
  W = 24 Macaulay matrix (3199 × 3199) mod p = 1000003 (w₀ = 806739) and mod p = 32003
  (w₀ = 11147): FLINT `nmod_mat.rank` and an independent numpy elimination agree;
  planted-zero control drops rank to 3198 as required. Script:
  `bundle_v3_1/jacobian_lean/chart_certificates/step3b_rank_lift.py` (6.5 min, 0.5 GB).
- t₁ = 0 slice: exact certificate over K₅ (degree 2, 75 K₅-terms), checked by an
  independent FLINT script; 5 negative controls fail as required.

## Provenance

- v3.1 supersedes v3.0 (bundled while the build was still running); §13 of GUIDE.md
  records what changed (the build, the fixed `Bridge` bug, the verification, verbose logs).
- The v2 corrected-commit proposal is **not** applied; `branch_c/` on repo main is untouched
  by this package.
- Nothing has been pushed, published, uploaded, deposited or minted.
