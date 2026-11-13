# G2 enactment — step record (2026-11-12)

**Branch:** `g2-enactment-step-record-2026-11-12` (off cloud main `a4eb466`).
**Status:** enacted on the branch. **NOT merged to main.** No email sent.
No GCP spend. No grade changes.

## Decision

**2026-11-12 ~20:56 CST, assistant under Brandon's standing full decision
autonomy** ("it's your call.. autonomy remember?"): the leg-9 G2 enactment
goes ahead **as a step record**, not waiting for the full unconditional GGHV
proof. Rationale: G2 gave CONDITIONAL GO on 2026-11-11 with enactment as
the next step; Leg 9b passed and the Zenodo DOI is published; the leg-9
result is verified (kernel-verified attempts 121/124, three-prime Singular
cross-check, DOI 10.5281/zenodo.24157382) and accurately gradable as a step
at Track F, F1, I1. Recording a verified step promptly with its correct
grade is the truth-seeking move; it does not claim the unconditional proof.
The mandate's post-proof paper update and author emails are a different,
larger step and still wait for the full proof.

**Basis verified for this enactment:**
- G2 validation: `g2_validation_report_2026-11-11.md` — CONDITIONAL GO,
  conditions G2-C1–G2-C6 (all discharged or applied below).
- Three-skill analysis: `leg9_success_analysis_2026-11-11.md` — K5 value
  independently re-verified; grade Track F, F1, I1; 8 changes proposed to
  the combined paper, 0 to the dicriticals paper.
- Leg 9b (G2-C2): DISCHARGED — `leg9b_results.json`, `all_singular_pass`
  and `all_flint_pass` both true. Calibration $p = 32003$ ($w_0 = 11147$,
  det $29127$); fresh small primes $10000019$ (det $6539686$), $10000103$
  (det $11653$), $10000139$ (det $5735547$); Singular and FLINT agree on
  all three. (Singular 4.3.1 cannot create a 61-bit-characteristic ring, so
  Leg 9b ran at small primes per the D1 amendment.)
- Zenodo (G2-C3, deposit half): PUBLISHED 2026-11-12 ~03:55 CST, DOI
  **10.5281/zenodo.24157382** (concept DOI 10.5281/zenodo.24157381), v1
  Dataset, CC-BY-4.0, 7 files, API-verified.
- Combined paper md5 verified against the G2 record before editing:
  `3ee925d7ba630bc2f64eb4a1bd377c7d` (repo copy and
  `~/workspace/combined-paper/` copy identical before enactment).

## Paper changes — combined paper, all STEP RECORD at Track F, F1, I1

File: `dicriticals-at-infinity/paper/combined_paper_final_2026-11-04.tex`
(16 lines changed). Every change below states the leg-9 result and its
grade and does NOT state or imply the unconditional proof, $(72,108)$
excluded unconditionally, or JC(2) proved. The value itself (~3.3M decimal
digits) is never typeset; every citation is by repo path + sha256 + DOI.

- **C-1 — new validation note, November 11, 2026 (front matter, after the
  November 4 note).** Per-attempt counts (G2-F1: attempt 121: 244,000
  equations, $M$ of 14,884,000 bits; attempt 124: 250,000 equations, $M$ of
  15,250,000 bits; "the two verification attempts", not "two consecutive");
  explicit-minor certificate wording + canonical-certificate parenthetical
  (G2-F2); ten fresh-prime checks qualified "per the driver's fresh-prime
  gate" (G2-F3) with the Leg 9b three-prime Singular verification added;
  DOI (G2-C3/G2-F5). Labeled in the note as a step record, enacted
  November 12, 2026, at Track F, F1, I1, with the explicit non-claims
  (no unconditional proof, no $(72,108)$ excluded unconditionally, no JC(2)).
- **C-2 — abstract, l.138.** Appended sentence: the determinant of the
  $3199\times3199$ maximal minor $M_S$ is now exhibited as an explicit
  element of $K_5$ (five rational coefficients, filed result.json + DOI);
  agrees with both primes above and ten fresh primes (driver's gate); three
  fresh small primes verified independently in Singular (Leg 9b; step record
  at Track F, F1, I1).
- **C-3 — §bc:sec:wholechart, "The instance" (inserted after l.1382, before
  the figure, per G2-F6).** New determinant-value paragraph: per-attempt
  counts, bit ranges numerators $1{,}124{,}076$–$1{,}124{,}083$,
  denominators $1{,}089{,}696$–$1{,}089{,}704$ (G2-F4), FULL sha256
  `e7813e7896fff29466461446ded89499e4dd17f8d7d2ccc9a071e8903e96795c` (G2-F5),
  DOI, six known primes + ten fresh primes (driver's gate) + three fresh
  small primes verified independently in Singular. Ends: "recorded here as
  a step record; it changes no grade and no theorem."
- **C-4 — §bc:sec:wholechart opening paragraph.** Appended sentence
  distinguishing the canonical certificate $1=\sum c_nF_n$ (still
  unexhibited, existence only proved) from the minor determinant (now
  exhibited). No new grade.
- **C-5 — epistemic table (§bc:sec:epistemic).** New row **C11**:
  $\det(M_S)$ exhibited as an explicit element of $K_5$; evidence: leg-9
  multimodular reconstruction, filed result.json (DOI); six known values
  (independently re-derived) + ten fresh primes (driver's gate); three fresh
  small primes verified independently in Singular (Leg 9b); step record,
  Track F, I1; grade **F1**. (G2-F12 noted: the row distinguishes the two
  strengths, it does not present them as equal.) "What is not claimed"
  amended by one sentence: the C11 minor determinant is distinct from the
  whole-chart certificate of that clause — the former is exhibited, the
  latter is not. The existing clause stays intact.
- **C-6 — open items.** Item (6) added as drafted: independent verification
  of the exhibited $\det(M_S)$ value at fresh primes in Singular (or
  Magma/Sage), against the filed result.json (DOI). Annotations: item (1)
  unchanged (rank computation C5, not the determinant value); item (2)
  likewise unchanged (a Lean formalization of the value itself is a
  separate, un-ordered job); item (6) is in part done (three fresh small
  primes verified independently in Singular, Leg 9b) — further primes,
  Magma/Sage, or fresh 61-bit primes via an independent implementation
  remain open.
- **C-7 — conclusion (paragraph l.1468; the plan's l.1466 is the section
  header — G2-F18).** Appended sentence with the G2-F7 replacement verbatim
  ("completing the branch-(c) explicit-minor certificate (§6.3(a) as
  amended: the minor determinant is now exhibited; the canonical whole-chart
  certificate remains unexhibited, its existence only proved)") and the
  G2-F8 full guard ("correctness and exhaustiveness of Proposition~4.3"),
  plus DOI and "(Step record; the exhibited value is Track F, F1, I1.)"
- **C-8 — abstract, no further change (checked, not proposed).** l.148
  ("The rank computation remains as independent corroboration") is still
  accurate; nothing else in the abstract was touched.

**G2 corrections applied in the paper texts:** F1 (per-attempt counts,
"the two verification attempts"), F2 (explicit-minor wording + canonical
parenthetical), F3 (driver-gate qualifier kept for the ten fresh primes —
Leg 9b verified three, not ten, in Singular — with the Leg 9b phrase added
where the plan gated it), F4 (exact bit ranges), F5 (full sha256 in C-3;
DOI in all six result.json citations: C-1, C-2, C-3, C-7, C11, item (6) —
this is the G2-C3 citation half, now DONE), F6 (C-3 location), F7/F8
(C-7 wording + full guard).

**One convention deviation, recorded:** the plan's convention says not to
import the "§6.3(a)" label into the paper except in the dated validation
note; G2-F7's explicit replacement text for C-7 uses "(§6.3(a) as amended:
…)". The G2 correction was followed verbatim — the parenthetical is the
guard against the misreading G2 flags as the worst risk, and it names the
sense in which "completing" holds.

**Dicriticals paper:** NO changes (plan Part B; Theorem R open; no
branch-(c)/K5/Macaulay/minor content). Part III of the combined paper:
no changes.

**Do-not-change list (plan Part D):** all honored — corollary
`bc:cor:gghv` stays conditional; scope guards stay; C5/C9/C10 grades
unchanged; canonical-certificate estimate untouched; no "(72,108) excluded
unconditionally" or JC(2) language; no a816 or rank-lemma changes.

## Analysis correction note (G2-C4)

`~/workspace/goals/gghv-dependency-closure/hidden_files/phase4/leg9_success_analysis_CORRECTION_2026-11-12.md`
(dated note; the analysis file itself is not rewritten):

- **F13:** Prop 2.1 (2a)→(2b) is **KERNEL modulo carried (2a)** (leg 3,
  `prop21_two_b_of_a` [triple]); (2a) itself still carried/unproved; the
  $l > 1$ statement is not covered by pinned `prop21_two`. Corrected in
  all three places (§3.2 table l.240; §3.4 item 5 l.282; §6.3 table l.531)
  and §3.4 item 5 reworded; binding item is (2a) itself.
- **F14:** nine-equation row — CONDITIONAL (P3 closed by leg 10, kernel;
  P6 absorbed; P1, P2 carried; P4 discharged inside the bridge via `hD2`,
  to be supplied at instantiation ($t = D_2/3$); P5 carried as `hFm4` in
  `p3_s6`). Both places (§3.2 l.242; §3.4 item 6 l.283).
- **F15:** Thm 7.3 row — "Thm 7.3 proved from named §7 data (conditional,
  leg 5); unconditional proof BLOCKED on Puiseux (leg 12 VERIFIED)."
  (§3.2 l.238.)

## Record addenda (G2-C5)

- **F16(i) — inventory:** dated 2026-11-11 addendum to the §6.3(a) entry
  in `hidden_files/phase4/gghv_full_assembly_inventory.md` (entry retained
  verbatim; "no feasible route exists" superseded; outside-rebuild clause
  removed by ruling; §6.3(a) as amended satisfied; grade F1/I1).
- **F16(ii) — protocol:** status line under the 2026-11-07 amendment in
  `hidden_files/phase3/phase3_rq_brief_and_protocol_2026-11-06.md`:
  "Satisfied 2026-11-11 (leg-9 SUCCESS, commit 87a9b93; analysis
  `leg9_success_analysis_2026-11-11.md`)".
- **F16(iii) — MANIFEST:** dated addendum to §4.12 in
  `gghv-dependency-closure/lean/MANIFEST.md` (C1(b) superseded in both
  halves; PARTIAL text verbatim). On this branch.
- **F16(iv) — CORRESPONDENCE.md R16 hybrid row:** NOT done here — addendum
  belongs at the campaign-leg filing, which is a separate G2-gated step.
- **R-3 (G2-F9, corrected):** GOAL.md status entry 2026-11-12 records G2
  launched, Leg 9b ordered, BOTH citation routes chosen, stop/start test
  PASSED ~12:20 CST, Zenodo DOI published, and the enactment decision.
- **R-4 (G2-F10):** dated-note addendum appended to
  `gghv-dependency-closure/leg9/LEG9_RESULT_2026-11-11.md` (no top-level
  `"verified"` key exists in the attempt/result files; per-attempt booleans
  live in `state.json`'s `attempts` list). Filed record text untouched.
  On this branch.

## Verification — recompile

Recompiled the amended TeX with the established toolchain (XeLaTeX,
TeX Live 2026, `latexmk -xelatex`): **exit 0, 0 TeX errors, 0 undefined
references/citations, 68 pages** (Nov 4 version: 67 pp.). Build run from a
scratch copy in `/tmp/g2-build-src` (the `~/workspace/combined-paper/`
tree + the amended TeX), output to `/tmp/g2-enactment-build/`; the
recompiled PDF there is a verification artifact only and is NOT filed into
the repo (D-10: a new paper version is produced by recompiling from amended
TeX at filing, after Brandon's approval of the enacted text).

**Finding (pre-existing, not caused by this enactment):** the repo's paper
directory has no `figures_ab/` (or `figures_c/`) subdirectory, so a build
directly from the repo copy fails on the missing figure
`figures_ab/fig1_newton_polygons.png` — the figures live in
`~/workspace/combined-paper/figures_ab/` and `figures_c/`. The Nov 4 PDF
in the repo was evidently built from the `~/workspace/combined-paper/`
copy. Filing should either vendor the figures into the repo paper
directory or record the `~/workspace/combined-paper/` tree as the build
source.

**Sync note:** the `~/workspace/combined-paper/` copy of the TeX is now
stale (it still has md5 `3ee925d7ba630bc2f64eb4a1bd377c7d`); syncing it with
the enacted repo copy is a filing-time step, not done on this branch.

## Diff summary (branch vs main `a4eb466`)

| File | Change |
|---|---|
| `dicriticals-at-infinity/paper/combined_paper_final_2026-11-04.tex` | C-1–C-7 (16 lines changed; C-8 no-change) |
| `gghv-dependency-closure/lean/MANIFEST.md` | F16(iii) addendum (+14 lines) |
| `gghv-dependency-closure/leg9/LEG9_RESULT_2026-11-11.md` | F10 dated-note addendum (+22 lines) |
| `gghv-dependency-closure/G2-ENACTMENT-STEP-RECORD_2026-11-12.md` | this report (new) |

Goal-workspace files (not in the repo; edited in place, not on the branch):
`hidden_files/phase4/leg9_success_analysis_CORRECTION_2026-11-12.md` (new),
`hidden_files/phase4/gghv_full_assembly_inventory.md` (F16(i) addendum),
`hidden_files/phase3/phase3_rq_brief_and_protocol_2026-11-06.md` (F16(ii)
status line), `GOAL.md` (R-3 status entry).

**Not staged or committed on this branch** (parent's uncommitted Joseph
work, left untouched): `gghv-dependency-closure/CORRESPONDENCE.md`,
`gghv-dependency-closure/gghv_full_assembly_inventory.md` (repo copy),
`gghv-dependency-closure/lean/gghv_full_central_gaps_2026-11-06.lean`,
untracked `JOSEPH-LEMMA-2-2_LOCATED_2026-11-12.md`,
`JOSEPH-2-2-PREMISE-VERIFICATION_2026-11-12.md`, `lean/Puiseux.lean`,
`lean/Puiseux/`. Note the repo-copy inventory addendum (F16(i)) was
applied to the hidden copy only, per the plan; the repo copy's addendum
should ride with the campaign-leg filing once the Joseph changes land, to
avoid mixing two authors' edits in one file.

## What still waits for the full proof

- The mandate bar: Theorem 2.1 with zero carried premises (0/20 fields
  discharged); [GGV5] enumeration completeness kernel; [GGV6] Thm 7.3
  unconditional (Puiseux + B0); Joseph 2.2 located (done 2026-11-12) or
  replaced from scratch, with its premise gaps (G1–G5) closed; cota chain
  discharged; Prop 3.12 / Remark 3.31 / four red rows / [GGV6] Prop 2.5
  settled.
- Post-proof sequence only: (1) update the papers (this step record is not
  that update); (2) email the four GGHV authors and ask for arXiv
  endorsement. Nothing goes out before the proof is done.
- Campaign-leg filing (legs 3, 7, 8, 10, 11, 12, 13 + leg 6 outcomes, A-4
  addenda, incl. F16(iv)) — separate G2-gated step, not part of this
  enactment.
- The analysis's Joseph Lemma 2.2 row ("NOT LOCATED") is stale for a reason
  outside G2-C4 (located 2026-11-12, premise VERIFIED WITH GAPS, premise
  stays CONDITIONAL); a separate addendum should record it.
- Open item (6) remainder: verification at further primes, in Magma/Sage,
  or at fresh 61-bit primes via an independent implementation.
