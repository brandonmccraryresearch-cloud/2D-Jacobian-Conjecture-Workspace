# Lean Build Status (v18)

## v18 Packaging Note (2026-09-28)

This tree (`branch_ab_v18/`) is derived from the published v17 (`branch_ab_v17/`,
commit 45dc9b3 plus the PR #2 README fix merged at 2a40ffd; unchanged since).
The v18 changes repair three items the v17 paper and
scripts left incomplete. Public on GitHub since 2026-09-28; not submitted to a
journal or preprint server; no archival deposit or DOI.

### What changed in v18

**Proposition 6.1 (m = 3, 5) is now proved exact, not just bounded.** The paper
proof shows the Belyi bounds 3 and 10 are sharp: in the normalization
α₀=β₀=α_m=1 the system has vector-space dimension 3 (m=3) / 10 (m=5), and the
eliminant in a_{m−1} is irreducible and separable over ℚ, so all d roots occur
(Galois-stable). New script `scripts/e5_exact_counts_m35.py` checks all of this
(Singular elimination + FLINT); ALL CHECKS PASS.

**Planted known-good E2 control** in `scripts/exact_obstruction_K5.py`: shifts the
E2 inhomogeneity so a planted (t0,s0,b0*) solves it, then confirms the machinery
reports consistency (7 conditions vanish, 35 minors vanish at t0,
condition-matrix rank 3 → 2, planted E2 directly solvable). A second cubic
planting (δᵢ·(t₁/t₀,₁)³ subtracted from bᵢ) keeps the minors homogeneous and
drops their rank from 6 to 5, testing the final rank-6 step.

**E3 everywhere-solvability check** in `scripts/exact_ranks_K5.py`: the single
left null vector of the 19×20 E3 Jacobian kills the quadratic inhomogeneity K(t)
identically, so E3 is solvable for every t.

`scripts/README.md` documents the new/changed scripts; `CHANGES_v18.md` (in this
directory) lists every changed file.

## v17 Packaging Note (2026-09-27)

This bundle is derived from the v16 upload (`branch_ab_final_v16.zip`, top directory `v13_bundle/`).
Every v16 file is kept. The changes are listed below. Nothing has been published, uploaded or
deposited.

### What changed

**The m = 7 top-layer classification is proved in Lean.** This is Proposition 6.1 for m = 7 in the
normalized chart (`ChartClassification`), the form the main theorem uses. The degree-35 eliminant 𝒲
and the cases m = 3, 5 of Proposition 6.1 are not formalized.

- `BranchAb.chartClassification_holds : ∀ (L : Type*) [Field L] [CharZero L], ChartClassification L`
  discharges the hypothesis of `main_theorem_of_chart`.
- `BranchAb.main_theorem` states the NewtonNF2 form of Theorem 1.1 with no hypothesis.
- The statement `ChartClassification` (`lean/Jacobian/BranchAbChart.lean`) is byte-identical to v16.

**New files.**

- `lean/Jacobian/ChartProof/`, 12 modules:
  - `Reflect.lean`, hand-written, 6.2 KB. It is a kernel-evaluable reflective checker (`toPolyK`,
    `eq_of_toPolyK`, `lc_zero`) built on the verified `Lean.Grind.CommRing` normalizer of Lean core.
  - 11 generated modules, 6.5 MB in total, with 111 step theorems.
- `lean/certgen/chartproof/`: the generator (Python, SymPy, python-flint), its data files,
  `regenerate_chartproof.sh` and `README_chartproof.md`. `saturation_check.py` and its output
  `saturation_Q.sing` give context for Step 2 of the proof and are not used by it.
  `independent_check.py` re-verifies all 111 identities from the Lean text, independently of the
  generator and of Lean.
- `logs/chartproof_{build,axioms,controls,regeneration,saturation,independent_check}.log` (the same
  files are mirrored in `lean/logs/`) and `logs/regeneration_check_v17.log`.
- `paper/v17_patch.py`, which records every TeX change.

**Changed files in `lean/`.**

- `Jacobian.lean`: adds `import Jacobian.ChartProof.Final`.
- `AxiomsAudit.lean`: adds 4 `#print axioms` lines.
- `verify_branch_ab_lean.sh`: checks 44 theorems; adds a resource note.
- `controls.sh`: adds 6 ChartProof controls; the number of parallel jobs is set by `CONTROLS_JOBS`.
  A rejection now counts only if Lean reports the expected error; for the ChartProof certificate
  perturbations that is the kernel's verdict that the identity is false. An out-of-memory kill or a
  failed import counts as a failure; v16 counted every nonzero exit as a rejection.
- `certgen/check_regeneration.sh`: also runs `chartproof/regenerate_chartproof.sh` (set
  `WITH_CHARTPROOF_REGEN=0` to skip it).
- `CHANGES.diff`: v17 addendum, with the unified diff of the hand-written Lean-side files against v16.
- `README.md`, `CLASSIFICATION_STATUS.md`, `MERGE_README.md`.
- `MD5SUMS`: now covers every file in `lean/`. The v16 list omitted `AxiomsAudit.lean`,
  `MERGE_README.md` and `gen_listings.py`.

**Changed files elsewhere.**

- `scripts/gen_listings_v10.py`: three new listings. The begin/end markers now match whole labels only,
  so `lst:chart` can no longer match inside another label's markers.
- `correspondence_guide/CORRESPONDENCE_GUIDE.md`: the m = 7 chart classification (Prop. 6.1) is marked
  proved, with its scope; new verification rows.
- `paper/`: the TeX, PDF and auxiliary files (see "Paper build notes" below).

### Verification performed for v17

All runs are from 2026-09-27, in a cloud container with 8 GB RAM and a cgroup limit of 6.27 GB, using
Lean v4.34.0 and Mathlib v4.34.0.

| Check | Result | Evidence |
|---|---|---|
| Sequential build of the 11 generated ChartProof modules (`Reflect.lean` was built before, as a dependency) | PASS; 25.3 min wall clock; peak 5.44 GB (`Stage2_g7`) | `logs/chartproof_build.log` |
| `lake build Jacobian` with the v17 root file | PASS (9,032 jobs) | `logs/chartproof_build.log` |
| `verify_branch_ab_lean.sh` (v17): build, static scan, `#print axioms` on 44 theorems | ALL CHECKS PASSED; 44 of 44 on the standard axioms | `logs/chartproof_axioms.log` |
| `lake env lean AxiomsAudit.lean` (v17) | 13 declarations, standard axioms only | `logs/chartproof_axioms.log` |
| `controls.sh` (v17), `CONTROLS_JOBS=1` | 14 of 14 as expected; each of the 4 ChartProof perturbations is rejected with the kernel's `decide` verdict; 1,115 s | `logs/chartproof_controls.log` |
| `certgen/chartproof/regenerate_chartproof.sh` | PASS: 4 data files and 11 modules byte-identical; 105 identities re-verified in SymPy | `logs/chartproof_regeneration.log` |
| `certgen/check_regeneration.sh` (v17), in full | PASS: descent certificate and generated Lean files byte-identical; PARI/GP span check (5 checks); ChartProof regeneration; 489 s | `logs/regeneration_check_v17.log` |
| `certgen/chartproof/saturation_check.py` (Singular over ℚ; context only) | PASS: `(S₁₁..S₁₆) : y₇^∞ = (S₁₁..S₁₆) : y₇³ = (g)`; 5 solutions | `logs/chartproof_saturation.log` |
| Paper, XeLaTeX (TeX Live 2023/Debian), 3 passes | 0 errors, 0 undefined references, 0 overfull boxes (5 underfull, 3 of them as in v16); 28 pages | `paper/branch_ab_elimination_v3.log` |
| Independent audit by a separate agent that had not seen the work: SymPy re-derivation of Steps 1–5 of the proof, re-verification of all 111 identities parsed from the Lean text, static scan, documentation cross-check | No mathematical defect found. The documentation defects it found are fixed in this bundle, except that "Remark 6.4" and "§6.4" share a number (the paper numbers remarks within sections) | its checker ships as `certgen/chartproof/independent_check.py` |
| `certgen/chartproof/independent_check.py` | PASS: 111 of 111 identities hold over ℤ (105 `lc_zero`, 6 cancellations); a perturbed copy fails | `logs/chartproof_independent_check.log` |

**Build environment caveat (as in v8 and v13).**

- All Lean runs above used a copy of `lean/` in which the 48 descent certificate modules
  `Jacobian/Descent/{E3,E3red,E4}/*.lean` import four Mathlib modules instead of `import Mathlib`.
  This keeps the build within the memory limit.
- The copy differs from this bundle in those 48 import lines only (`diff -r`, 2026-09-27).
- `Jacobian/ChartProof/` is byte-identical in the copy and in this bundle.

**Not re-run for v17.** None of the following files changed:

- the from-scratch build of the pre-existing 95 modules with `import Mathlib` (the v8 referee build is
  carried over);
- the scripts in `scripts/` other than `gen_listings_v10.py` (v13 records).

**Paper build notes.**

- `paper/v17_patch.py` is applied to the v16 TeX. It changes:
  - the abstract and the introduction overview;
  - §1.3, now titled "Logical status" instead of "Conditional status";
  - the status remark for `ChartClassification`;
  - three "given Proposition 6.1" qualifiers;
  - the attribution and the computational archive;
  - the first sentence of the remark "What remains", which now says that only Corollary 1.2 (the
    application to the Jacobian conjecture) depends on GGHV Proposition 4.3, as Remark 1.3 does;
  - and it inserts the new §6.4: Theorem 6.5, Remarks 6.6–6.7 and listings 16–18.
- `scripts/gen_listings_v10.py ../lean branch_ab_elimination_v3.tex` then fills the listings.
  - The 18 pre-existing listings are unchanged in content.
  - Listings after §6.4 are renumbered 19–21, and equation numbers after (7) shift by one.
- The same engine produces 25 pages from the unpatched v16 source, so §6.4 adds 3 pages. The v16 PDF
  has 24 pages because it was built with TeX Live 2026.
- Noto Sans (Regular, Bold, Italic, Bold Italic) and Noto Sans Mono Bold were missing in this container
  and were installed from `github.com/googlefonts/noto-fonts`. Builds with other copies of these fonts
  may break lines slightly differently.

**Generator hygiene.** `gen_v2.py`, `gen_final.py` and `parse_chart.py` read and write Lean text as
explicit UTF-8, and their size messages count UTF-8 bytes. The regeneration check above was run after
this change and is byte-identical.

**Superseded below.** The v13 sections that follow are kept as a record. In particular, their
"Source Integrity" statement (Lean sources byte-identical to v8) no longer holds for v17. See "What
changed" above.

---

## v13 Packaging Note (2026-09-27)

Repairs relative to v12 (all in a clean extraction; v12 bundle unchanged):
- `scripts/audit_chart_v8_rerun.py`: handles `chartpoint.json`'s actual `P`/`Q` key layout; rerun passes 17/17 hypotheses and 17/17 conclusion coordinates.
- `scripts/C1_layer_reduction.sing`: appended `quit;` so the job terminates; rerun: identity residual 0.
- `scripts/source_gate_verify.py`: honors `sys.argv[1]`; rerun against GGHV v1: SOURCE GATE PASS.
- `scripts/gen_listings_v10.py`: `extract_definition()` recognizes `noncomputable`; `e2_t0` now mechanically counts 19 `r2_*` hypotheses and emits range `(r2_1_1)...(r2_19_37)`; `topB` regenerates with its source `noncomputable` prefix. TeX regeneration diff vs v12 shows exactly the two intended listing changes.
- `scripts/README.md`: restored/updated (working directories, argv behavior, chart-audit key mapping, listing-generator invocation).
- Paper §11: blind-replication paragraph and `ClaudeBlind` bibliography entry now name commit `37c73b67` (2026-09-25), verified via the GitHub API.
- Paper PDF rebuilt: XeLaTeX, 3 passes, 0 errors, 0 undefined refs/citations, 24 pages. Toolchain note: v12's PDF was built with Debian TeX Live 2023, which the platform removed before this pass; the v13 build uses TinyTeX (TeX Live 2026). The 25→24 page shift is engine line-breaking only — the TeX source diff vs v12 is exactly the four intended changes above (two listing fixes, two §11 citation additions), and extracted PDF text contains no `[?]` or `??`.
- Every shipped executable script rerun 2026-09-27 with captured exit codes: `audit_chart_v8_rerun.py`, `C1_layer_reduction.sing`, `source_gate_verify.py`, `gen_listings_v10.py`, `belyi_count.py`, `belyi_counts_m357.py`, `verify_msolve_param.py`, `compare_V.gp` (via cypari2/PARI, `gp` binary unavailable in this runtime), `exact_ranks_K5.py`, `exact_obstruction_K5.py`, `a816_full.sing` — all PASS. `gen_listings_v9.py` is superseded by `gen_listings_v10.py` (kept for provenance only).

## Source Integrity

The Lean 4 sources in `lean/` are **byte-identical** to v8 (verified by `diff -r`):
- `lean/Jacobian/` — all 95 `.lean` files + `Jacobian.lean`
- `lean/certgen/` — certificate generation scripts
- `lean/lakefile.toml`, `lean/lean-toolchain`, `lean/lake-manifest.json`

## Referee's Independent Build (v8)

The pre-submission reviewer (Claude/Anthropic) built all 95 modules from scratch:
- **Result**: 95 of 95 modules, no errors, no `sorry`
- **Axioms**: standard axioms only (`propext`, `Classical.choice`, `Quot.sound`)
- **Caveat**: To fit a memory cap, 48 certificate modules were rebuilt with only import lines changed

This build carries over to v13 as-is because the sources are unchanged.

## Shipped Logs

The logs in `logs/` are from the v8 packaging:
- `lake_build_from_scratch.log` — original build (predates chart modules)
- `run_all_first_pass.log`, `run_all_with_chart.log` — verification runs
- `verify_from_scratch.log`, `verify_with_classification.log` — axiom audits
- `chart_cas.log` — Singular computations for ChartClassification
- `controls.log` — negative controls (6/6 PASS)
- `regeneration_check.log` — certificate regeneration check
- `audit_chart_v8_rerun.log` — chart audit rerun

**Note**: These logs do not include build output for `BranchAbChart`, `BranchAbMain`, or `BranchAbNewton` because they were generated before those modules' build output was captured. The referee's 95/95 build (above) did include them.

## Reproducing the Build

On a machine with sufficient RAM (the referee built with a 6GB memory cap):
```bash
cd lean
lake exe cache get
LEAN_NUM_THREADS=1 lake build
```

Expected: all 95 modules compile with no errors and no `sorry`.

Note: `lake build` does not accept a `-j` flag. Use `LEAN_NUM_THREADS=1` to limit to a single job.
