# Sealed Answer Key — 2D Jacobian Conjecture Workspace

**Document version:** 1.0
**Date:** 2026-10-07
**Classification:** SEALED — Do not open until all replication runs are complete and recorded.

---

## Rules

1. **Do not open this document** until you have run every step in `BLIND_REPLICATION_GUIDE.md` for the branch(es) you are replicating and recorded all outputs.
2. Compare your recorded outputs against the expected values below, branch by branch.
3. **Never edit your recorded outputs** after opening this key. If you find a discrepancy, follow the procedure in the guide (§6).
4. A mismatch on any value below is a finding, not a failure of the replication — report it.

---

## Branch (a,b) — Expected Values

### A1. Checksum verification

| Check | Expected |
|---|---|
| `md5sum -c CHECKSUMS.md5` | All 418 entries OK, 0 failures |
| `sha256sum -c CHECKSUMS.sha256` | All 418 entries OK, 0 failures |

### A2. Master verification script (`verify_v19.sh`)

| Check | Expected |
|---|---|
| Final summary | `PASS=18 FAIL=0` |
| Exit code | 0 |

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
| `#print axioms` on all new theorems | Exactly `[propext, Classical.choice, Quot.sound]` |
| `sorry` count | 0 |
| `native_decide` in build roots | None |
| Negative controls (`controls_a816.sh`) | 9 of 9 rejected/flagged correctly |

### A10. Paper build

| Check | Expected |
|---|---|
| Page count | 34 pages |
| Missing glyphs | 0 (Fira Sans/Mono/Math only, verified by `pdffonts`) |
| LaTeX errors | 0 |
| Undefined references | 0 |

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
| Matrix dimensions | 3199 × 3199 |
| Nonzero entries (nnz) | 105,807 |
| Rank mod 1000003 | 3199 (full row rank) |
| Rank mod 32003 | 3199 (full row rank) |
| Lean kernel theorems | 6,398 (all pass) |
| Lean axioms | `[propext]` only |
| Negative control | Rejected (exactly 1 bit flipped → rank drops) |

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
| A2 PASS=18 | `branch_ab_v19/verify_v19.sh` output |
| A3 Belyi counts | `belyi_counts_m357.py` output; paper Prop 6.1 |
| A4 ranks 17/18/12 | `exact_ranks_K5.py` output |
| A5 35 minors | `exact_obstruction_K5.py` output; `logs/k5_minor_certificate.json` |
| A6 eliminant | `scripts/b26_m5_eliminant/`; `B26Irred.lean` |
| A7 counts 10/3 | `B26Count.lean` |
| A8 76/3464/56 | `scripts/a816_certificate/a816_lift.txt` |
| A9 axioms | `verify_branch_ab_lean.sh` output |
| A10 34 pages | `branch_ab_v19/paper/` build log |
| C2 3199×3199 | `branch_c/rank_lemma_check/` outputs |
| C2 6,398 theorems | Lean build log |

---

## Document history

- v1.0 (2026-10-07): Initial sealed answer key. Companion to `BLIND_REPLICATION_GUIDE.md` v1.0.
