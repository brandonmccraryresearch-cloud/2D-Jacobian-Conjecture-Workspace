# Reproduction Answer Key — 2D Jacobian Conjecture Workspace

**Document version:** 1.2
**Date:** 2026-10-12 (version 1.0: 2026-10-07, under the name `ANSWER_KEY.md`)
**Use:** Do not open until all runs of `REPRODUCTION_GUIDE.md` are complete and recorded. This key belongs to a
re-execution protocol (independence level I1, see the guide's §1); the project's scripts print most of these values
themselves. For the blind, independent replication see `JC2D-branches_a_b_c_unified/replication/`, which has its own
key.

---

## Rules

1. **Do not open this document** until you have run every step in `REPRODUCTION_GUIDE.md` for the branch(es) you are replicating and recorded all outputs.
2. Compare your recorded outputs against the expected values below, branch by branch.
3. **Never edit your recorded outputs** after opening this key. If you find a discrepancy, follow the procedure in the guide (§6).
4. A mismatch on any value below is a finding, not a failure of the replication — report it.

---

## Branch (a,b) — Expected Values

### A1. Checksum verification

| Check | Expected |
|---|---|
| `md5sum -c CHECKSUMS.md5` | All 478 entries OK, 0 failures |
| `sha256sum -c CHECKSUMS.sha256` | All 478 entries OK, 0 failures |

Version 1.1 of this key said 418. On main at commit `3e7c180` (2026-10-11) the manifests had 418 entries but failed on
`verify_v19.sh`: PR #14 had changed that script without updating the manifests. They also did not list the 55
route-C Lean files (`lean/Jacobian/A816C/`). The manifests were regenerated on 2026-10-12.

### A2. Master verification script (`verify_v19.sh`)

| Check | Expected |
|---|---|
| Final summary, Singular installed, no `lean/.lake` | `PASS=18 FAIL=0` |
| Final summary, Singular not installed | `PASS=15 FAIL=0` (three steps print `SKIP`) |
| Final summary, `lean/.lake` present | one more `PASS` (`lake build`) |
| Exit code | 0 |

On main at commit `3e7c180` the script gave `PASS=15 FAIL=3` (both manifests, and the page count of 34 against an
expected 35). Both causes are fixed on 2026-10-12.

### A3. Belyi counts (`belyi_counts_m357.py`)

| m | Covers | Chart points |
|---|---|---|
| 3 | 1 | 3 |
| 5 | 2 | 10 |
| 7 | 5 | 35 |

The script prints lines of the form `m={m}: ... covers = {q} ... chart points = {m*q}`. Verify the covers and chart points match the table above. Remainder must be 0 in all cases.

### A4. Exact K₅ ranks (`exact_ranks_K5.py`)

| Layer | Expected rank |
|---|---|
| E4 | 17 |
| E3 | 18 |
| E2 | 12 |

Additional assertions in the script:
- E4 kernel is 2-dimensional
- E3 left nullspace is 1-dimensional
- E3 is solvable for every t (the script asserts this)

### A5. Exact obstruction (`exact_obstruction_K5.py`)

| Check | Expected |
|---|---|
| 35 minors at rank 6 | All 35 determinants nonzero |
| Certificate status | `PASS` |
| Byte-reproducibility | Certificate file byte-identical before and after re-run |

The certificate JSON (`logs/k5_minor_certificate.json`) must have:
- `status`: `"PASS"`
- `matrix_35x6`: 35 rows × 6 columns
- `rank`: 6
- `pivot_rows`: 6 distinct rows
- `monomial_basis`: `["t1^5","t1^4*t2","t1^3*t2^2","t1^2*t2^3","t1*t2^4","t2^5"]`

### A6. B2.6 eliminant (G1)

The exact m=5 eliminant:

$$T_5(a_4) = 9a_4^{10} + 37200a_4^5 + 95051008$$

| Check | Expected |
|---|---|
| $T_5$ irreducible over $\mathbb{Q}$ | True (Lean: `B26Irred.lean`, kernel-checked) |
| $T_3 = 3X^3 - 32$ irreducible over $\mathbb{Q}$ | True (Lean: `B26Irred.lean`, kernel-checked) |
| Discriminant of $9z^2 + 37200z + 95051008$ | $-2037996288$ |

Back-substitution formulas (must satisfy all 10 GB elements and 4 residuals mod $T_5$):
- $a_1 = (3a_4^5 + 13078)/(362a_4)$
- $a_2 = 3(5a_4^5 + 10816)/(181a_4^2)$
- $a_3 = 7(123a_4^5 + 70304)/(2172a_4^3)$

### A7. Exact chart counts (G2)

| Chart | Expected count |
|---|---|
| m=5 | Exactly 10 solutions |
| m=3 | Exactly 3 solutions |

(Lean: `B26Count.lean`, kernel-checked, over algebraically closed characteristic-zero fields.)

### A8. a₈,₁₆ certificate

| Check | Expected |
|---|---|
| Witness lines in `a816_lift.txt` | Exactly 76 |
| Total terms (all 76 lines) | 3,464 |
| Nonzero cofactors | 56 of 75 |
| Cofactor terms (lines 1–75) | 3,462 |
| Rabinowitsch tail terms (line 76) | 2 |
| Layer split (nonzero cofactors) | 17 / 18 / 18 / 3 (d=3,2,1,0) |
| Rabinowitsch tail content | `-a_8_16*z-1` |

### A9. Lean kernel checks

| Check | Expected |
|---|---|
| `#print axioms` on the 66 theorems of `verify_branch_ab_lean.sh` | Each a subset of `[propext, Classical.choice, Quot.sound]`: 64 use all three; `m5_a4_ne_zero` and `m3_a2_ne_zero` use `[propext, Quot.sound]` |
| `sorry` count | 0 |
| `native_decide` in build roots | None |
| Negative controls (`controls.sh`, v17) | 14 of 14 as expected: 3 accepted, 9 rejected, 2 `sorry` copies flagged (`lean/logs/chartproof_controls.log`; `lean/logs/controls.log` is an older run of 6 controls) |
| Negative controls (`controls_a816.sh`) | 9 of 9 as expected: 2 accepted, 6 rejected, 1 `sorry` copy flagged |
| Route C (`lean/verify_routeC.sh`, optional) | `routeC_a816` and `routeC_source` on `[propext, Classical.choice, Quot.sound]` or a subset; see `lean/logs/routeC_axioms.log` |

### A10. Paper build

| Check | Expected |
|---|---|
| Page count | 34 pages, the shipped PDF; 35 is accepted (see below) |
| Missing glyphs | 0 (Fira Sans/Mono/Math only, verified by `pdffonts`) |
| LaTeX errors | 0 |
| Undefined references | 0 |

**Page count.** The shipped PDF (`paper/branch_ab_elimination_v3.pdf`) has 34 pages. A 2026-10-12 build with TeX Live
2026 (TinyTeX) and the CTAN Fira fonts gives 34 pages and 0 missing glyphs. Version 1.1 of this key changed the value
to 35 after one other TeX Live 2026 installation produced 35 pages from the same source; it attributed the extra
page to PR #11, but the current source gives 34 in the build above. Line breaking depends on the installation, so
both 34 and 35 are accepted; record which you get.

---

## Branch (c) — Expected Values

### C1. Checksum verification

| Check | Expected |
|---|---|
| `md5sum -c CHECKSUMS.md5` (in `branch_c/`) | All entries OK, 0 failures |
| `sha256sum -c CHECKSUMS.sha256` (in `branch_c/`) | All entries OK, 0 failures |

### C2. Rank lemma check (`rank_lemma_check/run.sh`)

| Check | Expected |
|---|---|
| M₂₄ (`logs/build_matrix.log`) | 3199 × 6054, 239,154 nonzero entries; columns per generator Ψ 1308, Φ₁ 1071, Φ₂ 1071, Θ₁ 868, Θ₂ 868, Θ₃ 868 |
| Rank of M₂₄ mod 32003 (`logs/make_inverse.log`) | 3199 of 3199 rows: full row rank |
| Pivot block M_S (`logs/make_inverse.log`) | 3199 × 3199, 105,807 nonzero entries; C = M_S⁻¹ mod 32003 with C·M_S = I (FLINT) |
| Lean kernel theorems (`logs/check_logs.log`) | 6,398 = 2 × 3199 packed identities, all pass |
| Lean axioms | `[propext]` only |
| Kernel controls (`logs/check_logs.log`) | 5 of 5 rejected (`ctrl_fail_entry`, `_coeff`, `_index`, `_drop`, `_slot`: one change each to column 2561); the unchanged `ctrl_pass` passes with `[propext]` |
| Script controls | `exact_lean_vs_json.py`: 2 rejected; `compare_lean_conds.py`: 1 rejected at each prime |
| Final line of `logs/check_logs.log` | `RESULT: PASS` |

**Not reproduced by `run.sh`.**
- The rank of M₂₄ modulo 1000003 (also 3199, full row rank) and the ranks at W = 22, 23 (2277 and 2707, not full)
  are logged in `bundle_v3_1/jacobian_lean/chart_certificates/step3b_rank_lift.log`. Version 1.1 of this key listed
  "rank mod 1000003: 3199" for the 3199 × 3199 block; only M₂₄ was computed mod 1000003, and the pivot block was
  never checked at that prime.
- The independent replication (`JC2D-branches_a_b_c_unified/replication/`, target C3) recomputes all of these ranks
  in fresh code.
- Version 1.1 described the negative control as "exactly 1 bit flipped → rank drops". The controls are the ones
  listed above; none of them is a rank computation.

### C3. Branch (c) verification (`verify_branch_c.sh`)

| Check | Expected |
|---|---|
| Exit code | 0 |
| All sub-checks | PASS |

### C4. Bundle integrity

| Check | Expected |
|---|---|
| `bundle_v3_1/` byte-identity | Unchanged from v3.1 release (manifest verifies) |

---

## Traceability

Every value above is traced to a specific artifact:

| Value | Source |
|---|---|
| A1 checksums | `branch_ab_v19/CHECKSUMS.md5`, `CHECKSUMS.sha256` |
| A2 PASS=18 | `branch_ab_v19/verify_v19.sh` output (18 counted steps with Singular and without `lean/.lake`) |
| A3 Belyi counts | `belyi_counts_m357.py` output; paper Prop 6.1 |
| A4 ranks 17/18/12 | `exact_ranks_K5.py` output |
| A5 35 minors | `exact_obstruction_K5.py` output; `logs/k5_minor_certificate.json` |
| A6 eliminant | `scripts/b26_m5_eliminant/`; `B26Irred.lean` |
| A7 counts 10/3 | `B26Count.lean` |
| A8 76/3464/56 | `scripts/a816_certificate/a816_lift.txt` |
| A9 axioms | `verify_branch_ab_lean.sh` output; `lean/logs/axioms_verify_script_66.log` |
| A9 controls | `lean/logs/chartproof_controls.log`, `lean/logs/controls_a816.log` |
| A10 34 pages | the shipped `branch_ab_v19/paper/branch_ab_elimination_v3.pdf`; `verify_v19.sh` step 5 |
| C2 M₂₄ and M_S | `branch_c/rank_lemma_check/logs/build_matrix.log`, `make_inverse.log` |
| C2 6,398 theorems, controls | `branch_c/rank_lemma_check/logs/check_logs.log` |

---

## Document history

- v1.0 (2026-10-07): Initial sealed answer key. Companion to `BLIND_REPLICATION_GUIDE.md` v1.0.
- v1.1 (2026-10-08): A10 page count 34 → 35. PR #11 (merged 2026-10-07, Route R: lower-edge rigidity in Lean) added a page to `branch_ab_v19/paper/branch_ab_elimination_v3.tex`; recompiled with TeX Live 2026 yields 35 pages, 0 missing glyphs. All other values re-verified against current main (audit 2026-10-08).
- v1.2 (2026-10-12): Renamed `REPRODUCTION_ANSWER_KEY.md`, with the guide renamed `REPRODUCTION_GUIDE.md` (see the
  guide's §1: re-execution, independence I1). Corrections:
  - A1: the manifest count after regeneration (v1.1's 418 failed on `verify_v19.sh` and omitted the route-C files).
  - A2: `PASS=18` holds only with Singular and without `lean/.lake`; the other cases are listed.
  - A9: the axioms are a subset of the three standard ones, not exactly them (two theorems use two); the controls of
    `controls.sh` are listed; route C added.
  - A10: 34 pages, the shipped PDF; 35 accepted. v1.1's attribution of a 35th page to PR #11 is not reproduced.
  - C2: the 3199 × 3199 block is M_S, the pivot block of M₂₄ (3199 × 6054); "rank mod 1000003" belongs to M₂₄ and is
    not reproduced by `run.sh`; the controls are described as they are.
