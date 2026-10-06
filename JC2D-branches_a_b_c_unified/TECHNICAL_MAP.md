# Technical Map — JC2D Branches (a), (b), (c), Unified

Elimination of the degree-(72,108) candidate of GGHV Proposition 4.3, case (1),
for the two-dimensional Jacobian conjecture, branches (a), (b) and (c).

This document is the exhaustive guide to `JC2D-branches_a_b_c_unified/`: the
mathematics, every component, the symbolic and numerical eliminations branch by
branch, the trust base, and how to reproduce everything.

---

## 1. What this is

GGHV Proposition 4.3 (case (1)) lists the surviving configurations for a
counterexample pair to the planar Jacobian conjecture at degree pair (72,108).
In the repository's formalization they are organized as **branches**:

| Branch | GGHV normal form | Case | Status |
|---|---|---|---|
| (a), (b) | form (2) | degree-(8,28) | **Eliminated** — Lean `main_theorem`, no remaining hypothesis |
| (c) | form (1) | degree-(72,108) | **Closed under stated computational premises** — Lean proves `ChartEmptyC_T1ne0 → … → ¬∃ P Q λ`; the chart-emptiness premise itself is proved outside Lean (grade B) |

Both branches work over

    K₅ = ℚ[w]/(R),   R(w) = w⁵ − w⁴ + 3w³ + 3w² + 26,

R irreducible over ℚ (and mod 109). The Jacobian condition is `[P,Q] = λx²`
with `λ ≠ 0`.

**Scope.** This unified directory is the branch-elimination record for one case
(case (1)) of one proposition (GGHV Prop. 4.3). It is not a proof of the
two-dimensional Jacobian conjecture; it says nothing about the other cases of
Prop. 4.3, and nothing about the reduction from the conjecture to Prop. 4.3
(that reduction is external mathematics). Nothing here has been published,
uploaded, deposited or minted beyond what each branch package already records.

---

## 2. Directory layout

```
JC2D-branches_a_b_c_unified/
├── README.md                      # overview + reading order
├── TECHNICAL_MAP.md               # this file
├── TODO_correspondence_guide.md   # conditional to-do (NOT started)
├── branches_a_b/                  # branch-(a,b) package (v19, revised 2026-10-05; identical copy: /branch_ab_v19/)
│   ├── README.md
│   ├── BUILD_STATUS.md
│   ├── CHECKSUMS.md5 / CHECKSUMS.sha256
│   ├── CHANGES_v18.md / CHANGES_v19.md
│   ├── paper/                     # 33-page paper: branch_ab_elimination_v3.tex/.pdf
│   ├── scripts/                   # audit/analysis scripts + README; since 2026-10-05 also
│   │                              #   a816_certificate/, b22_structured/, b26_m5_eliminant/
│   ├── lean/                      # Lean 4 project: proof sources, generators, verify scripts
│   │   ├── Jacobian/ChartProof/   # the 12-module machine-checked proof (111 identities)
│   │   ├── Jacobian/B26/          # m = 3, 5 chart classifications (10 modules, 2026-10-05)
│   │   └── certgen/chartproof/    # exact generators + independent checks
│   ├── audits/                    # HLRE v5.0 audit + errata
│   ├── correspondence_guide/      # CORRESPONDENCE_GUIDE.md (exists for a,b)
│   ├── figures/                   # paper figures
│   ├── logs/                      # build, axiom, control, regeneration, saturation logs
│   └── verify_v19.sh              # one-command verification
└── branch_c/                      # branch-(c) package in the (a,b) paper format (v3.1)
    ├── README.md                  # format map: (a,b) component -> (c) location
    ├── BUILD_STATUS.md            # build + verification record
    ├── CHECKSUMS.md5 / CHECKSUMS.sha256
    ├── GUIDE.md                   # the comprehensive v3.1 guide (start here for branch c)
    ├── V3_1_PROVENANCE.md         # provenance of the v3.1 bundle
    ├── paper/
    │   ├── branch_c_elimination.tex / .pdf   # the 16-page elimination paper (2026-09-30)
    │   ├── README.md                         # paper build + status
    │   └── BRANCH_C_GUIDE.md                 # comprehensive v3.1 reference (paper-equivalent)
    ├── bundle_v3_1/               # the v3.1 bundle, byte-for-byte (manifest-verified)
    │   ├── GUIDE.md / README.txt / PARTS.txt / MANIFEST.sha256
    │   ├── jacobian_lean/         # Lean overlay + generators + certificates
    │   │   ├── Jacobian/BranchC/  # v1/v2 modules, Descent2R (505), T1Zero, Bridge, CondsC
    │   │   ├── certgen_c/         # exact generators (python-flint) + data
    │   │   ├── chart_certificates/# step-1/3/4 scripts + data (rank lift, identities)
    │   │   ├── AxiomsAuditBranchC.lean, BRANCH_C_LEAN_STATUS.md
    │   │   └── verify_branch_c_lean.sh, build_branch_c_lowmem.sh
    │   ├── logs/                  # every build/verify/control log (GUIDE.md §9 index)
    │   ├── diag/                  # procmon.py, guardrun.py, leanprof.sh, t1z_controls.py
    │   ├── profiling/             # Lean profiler findings + test files
    │   ├── muse_refutation/       # the false reduction_lemma axiom proves False
    │   └── v2_carryover/          # v2 audits, controls, checks, unapplied commit proposal
    └── verify_branch_c.sh         # wrapper -> bundle_v3_1/jacobian_lean/verify_branch_c_lean.sh
```

**Why `bundle_v3_1/` is kept intact.** `verify_branch_c_lean.sh` (steps 0–1)
requires `certgen/`, `certgen_c/`, `chart_certificates/` and `Jacobian/` as
siblings under `jacobian_lean/`, with byte-identical regeneration. Reorganizing
the interior would break the verified reproduction chain. The (a,b)-paper *format*
(paper / scripts / lean / audits / logs / checksums / verify) is therefore
provided at the `branch_c/` level — see the format map in `branch_c/README.md` —
while the bundle interior is untouched.

---

## 3. Branches (a) and (b) — elimination

GGHV normal form (2), degree-(8,28) case. Package: `branches_a_b/` (= `branch_ab`, the v19 package, revised
2026-10-05). The identical copy `branch_ab_v19/` at the repository root is the path the Zenodo record cites.

### 3.1 Symbolic elimination (Lean 4)

- `chartClassification_holds`: every solution of the 17-equation normalized chart
  (`ChartClassification L`) is one of the **five K₅-conjugate points** — the m = 7
  case of Proposition 6.1. Kernel-checked, depending only on `propext`,
  `Classical.choice`, `Quot.sound`.
- `BranchAb.main_theorem`: the NewtonNF2 form of Theorem 1.1 **with no remaining
  hypothesis** (v19 concludes `b_{12,24} = 0`; `a_{8,16} = 0` is an independent
  rigidity corollary).
- `lean/Jacobian/ChartProof/`: the 12-module machine-checked proof — Reflect plus
  11 generated modules, **111 step theorems**.
- `lean/Jacobian/B26/` (2026-10-05): the m = 3 and m = 5 chart classifications over any field of characteristic 0.
  `m3_chart_iff` and `m5_chart_iff` say the system holds iff T(a_{m-1}) = 0 plus explicit back-substitution; the
  squarefree lemmas show T has no repeated root. The main theorem does not use them.
- `verify_branch_ab_lean.sh`: 53 theorems (44 until 2026-10-05, plus the 9 B26 theorems), each using only standard
  axioms (`lean/logs/axioms_verify_script_53.log`).
- Controls: 14/14 as expected (3 unmodified ACCEPT, 9 perturbed REJECT, 2 sorry
  copies flagged).

### 3.2 Numerical elimination (certificates and computation)

- The 33-page paper is organized around **four certificates**, with the 35-minor
  span argument and the characteristic-zero transfer made explicit (v19).
- `scripts/a816_full.sing`: `a_{8,16} = 0` forced (G[1] = 1 once E1 is included).
- `scripts/a816_certificate/` (2026-10-05): the explicit identity $a_{8,16}^2=\sum_k H_k e_k$ over K₅ (76 cofactors,
  3464 terms), checked exactly by Singular and by python-flint, with negative controls (Corollary 1.2).
- `scripts/b22_structured/` (2026-10-05): the c-recursion form of the chart system, validated exactly at the K₅ point.
- `scripts/belyi_count*.py`: the m = 3 / m = 5 Belyi bounds sharp (vdim 3/10,
  irreducible separable eliminants).
- `logs/k5_minor_certificate.json`: machine-readable 35×6 K₅ minor matrix with
  rank-6 certificate.
- 111/111 identities verified over ℤ (`independent_check.py`, ~2 s); saturation
  over ℚ via Singular.

### 3.3 Paper and verification

- `paper/branch_ab_elimination_v3.pdf` (33 pp, XeLaTeX, TeX Live 2026; revised 2026-10-05).
- `verify_v19.sh`: one command. It checks the checksums, runs the scripts, checks the 111/111 identities, builds the
  paper, and since 2026-10-05 also runs the a₈,₁₆ certificate checks, the B26 regeneration and statement checks, and
  the B2.2 validation.
- `correspondence_guide/CORRESPONDENCE_GUIDE.md`: proof elements mapped to their
  Lean formalization (exists for branches (a,b)).
- Published: Zenodo 10.5281/zenodo.23023490 (v19, preprint).

---

## 4. Branch (c) — elimination

GGHV normal form (1), degree-(72,108) candidate. Newton polygons:

    N(P) = conv{(0,0),(1,0),(8,14),(8,16),(0,8)}
    N(Q) = conv{(0,0),(2,1),(12,21),(12,24),(0,12)}

Package: `branch_c/` (v3.1, 2026-09-29). Comprehensive reference:
`branch_c/GUIDE.md` (§1 verdict, §2 the proof bridge by bridge, §3 the five
steps, §5 the computational structures, §5.9 the rank lemma, §9 the log index).

### 4.1 The five steps (as specified; all done)

| Step | Task | Status | Where |
|---|---|---|---|
| 1 | Certify `lower_c`'s ideal, not the pipeline's | **Done.** Exact over K₅ on the slice t₁ = 0 (FLINT, no Singular, 3 controls); modular on the whole chart (𝔽₁₀₁, 𝔽₁₀₀₀₀₀₃, 𝔽_{109⁵}) | `bundle_v3_1/jacobian_lean/chart_certificates/step1/` |
| 2 | Lean lemmas for the E₀, E₋₁, E₋₂ eliminations | **Done in Lean**, kernel-reflected, whole chain E₄…E₋₂ (`Descent2R`, 505 modules). `Bridge`: `DescentClaimC ⇐ ChartEmptyC` | `bundle_v3_1/jacobian_lean/Jacobian/BranchC/Descent2R/`, `CondsC.lean` |
| 3 | Canonical certificate over K₅ | **Not built (measured).** Hadamard bound 4.39 M digits; estimated heights 2.0–2.7 × 10⁵ digits. Replaced by an existence proof (step 4) | `chart_certificates/STEP3_4_CHART.md` §1 |
| 4 | Exact check with FLINT | **Done.** (a) t₁ = 0 certificate, exactly; (b) whole chart: exact finite-field ranks at two primes (FLINT + independent numpy elimination) proving a certificate exists over K₅ (rank lemma); (c) exact identity of the chart generators | `step1/check_certB_lowerc.py`, `step3b_rank_lift.py`, `step3c_chart_identity.py` |
| 5 | Check in Lean, or label | **Stratum t₁ = 0 kernel-checked** (`T1Zero`). **`ChartEmptyC ⇐ ChartEmptyC_T1ne0` in Lean** (`Combine`). `ChartEmptyC_T1ne0` proved **outside** Lean (step 4b) | `Jacobian/BranchC/T1Zero/` |

### 4.2 Symbolic elimination (Lean 4)

All modules built; `verify_branch_c_lean.sh` passes (exit 0); `#print axioms` shows
only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`/`axiom`/`native_decide`.

| Component | Modules | What it proves |
|---|---|---|
| v1/v2 (`Degree19`, `LayerE2`, `LayersGen`, `Edge19`, `OmegaSquare`, `OmegaEdge`, `DescentClaim`, `Descent/**`, `Rank/**`) | 162 | Layer identities, top layer, t₂ ≠ 0, normalization to the chart b_{12,22} = 1 — `DescentClaimC`'s hypotheses (`main_theorem_c_of_claim`) |
| `Descent2R/Facts`, `Vals_*`, layers L4, L3, L2c, L1, L0, Lm1, Lm2 | 505 | The E₄…E₋₂ eliminations by kernel reflection |
| `CondsC` | 1 | The twelve chart conditions |
| `Descent2R/Main` (`chart_descent_refl`) | 1 | Main descent reflection (1243 jobs, 2,298 s) |
| `Descent2R/Bridge` | 1 | `DescentClaimC ⇐ ChartEmptyC` (built after a bug fix, §13) |
| `T1Zero` (`Defs`, `Sq`, `F_*`, `P_*`, `Final`, `Main`) | 14+1 | `chartEmpty_t1_zero`: no common zero on the stratum b_{11,20} = 0; 5 negative controls fail as required |
| `T1Zero/Combine` | 1 | `ChartEmptyC ⇐ ChartEmptyC_T1ne0` — isolates exactly what Lean does not check |

Net Lean theorem (standard axioms only):

    main_theorem_c_of_chartEmpty_T1ne0 :
      ChartEmptyC_T1ne0 L → ¬∃ P Q λ, λ ≠ 0 ∧ NewtonNFc P Q ∧ jac P Q = C λ * X 0 ^ 2

### 4.3 Numerical elimination (certificates and rank computations)

- **Step 1** (`chart_certificates/step1/`): `certB_lowerc.json` — exact certificate
  over K₅ on the slice t₁ = 0 (degree 2, 75 K₅-terms, heights ≤ 9,681 digits),
  produced by `certB_lowerc.py` (pivots from mod-p RREF, exact FLINT solve) and
  checked by an independent script (`check_certB_lowerc.py`); controls: perturbed
  coefficient, Θ₃ dropped, the pipeline's generators — all False as required.
  Whole-chart modular certificates: 𝔽₁₀₁ (3,661 terms), 𝔽₁₀₀₀₀₀₃ (3,688 terms),
  𝔽_{109⁵} (102,097 terms; R irreducible mod 109).
- **Step 4b — the rank lemma** (GUIDE.md §5.9): let A = ℤ_(p)[w]/(R), free of rank
  5, φ: A → 𝔽_p with R(w₀) ≡ 0. If φ(M) has full row rank N, then M has full row
  rank over K₅ — some N×N minor has det φ(M_S) = φ(det M_S) ≠ 0, so M_S is
  invertible over K₅. Full row rank is the nonvanishing of a minor, an *open*
  condition, which is why it lifts (mere *consistency* of the Macaulay system does
  not lift — cf. `muse_refutation/`).
  Instance (`step3b_rank_lift.py`, 6.5 min, 0.5 GB): at W = 24 the Macaulay matrix
  is 3199 × 3199 of full row rank mod p = 1000003 (w₀ = 806739) **and** mod
  p = 32003 (w₀ = 11147); FLINT `nmod_mat.rank` and an independent numpy
  elimination agree; planted-zero control drops rank to 3198. Hence
  `ChartEmptyC`, hence `ChartEmptyC_T1ne0`.
- **Generators** (`certgen_c/`): `lower_c.py` writes `conds_c.json` (the twelve
  conditions); every generated identity is first checked in Python by exact
  integer arithmetic, and the generator asserts term-by-term equality with the
  conditions Lean derives.

### 4.4 Grades (HLRE)

| Claim | Grade | Basis |
|---|---|---|
| DescentClaimC's hypotheses (layers, top layer, t₂ ≠ 0, normalization) | **A** | Lean (v1/v2) |
| `DescentClaimC ⇐ ChartEmptyC` | **A** | Lean kernel reflection, built, axioms audited |
| Stratum b_{11,20} = 0 empty | **A** | Lean kernel (`T1Zero`), 5 negative controls |
| `ChartEmptyC ⇐ ChartEmptyC_T1ne0` | **A** | Lean (`Combine`) |
| `ChartEmptyC` (whole chart, all char-0 L) | **B** | Rank lemma + two-prime, two-implementation ranks + input checks |
| Canonical K₅ certificate heights | **C** (estimate) | Hadamard bound + extrapolated height estimate |

---

## 5. How the branches relate

- Branches (a)/(b) are GGHV normal form (2); branch (c) is normal form (1). They
  are disjoint cases of the same Prop. 4.3 case-(1) analysis.
- Both eliminations work over the same field K₅ = ℚ[w]/(R),
  R = w⁵ − w⁴ + 3w³ + 3w² + 26, and both exclude a pair with `[P,Q] = λx²`, λ ≠ 0.
- (a,b): the Lean formalization is complete — `main_theorem` has no remaining
  hypothesis. (c): Lean proves everything down to `ChartEmptyC_T1ne0`; that
  premise is discharged outside Lean by the rank computation (grade B).
- The (a,b) Lean project is the *base* the branch-(c) overlay builds on:
  `verify_branch_c_lean.sh` step 0 fingerprints the branch-(a,b) prerequisites
  (`certgen` inputs, 54 Descent E4/E3red/E3 files) before building branch (c).

---

## 6. Trust base

| Layer | Branches (a,b) | Branch (c) |
|---|---|---|
| Lean kernel + Mathlib v4.34.0; axioms `propext`, `Classical.choice`, `Quot.sound` | 44 theorems audited (`logs/chartproof_axioms.log`); 53 since 2026-10-05, with B26 (`lean/logs/axioms_verify_script_53.log`) | 53 theorems audited (`bundle_v3_1/jacobian_lean/axioms_branch_c.log`) |
| No `sorry` / `axiom` / `native_decide` | `grep`-checked | `verify_branch_c_lean.sh` step 4 |
| Symbolic elimination | ChartProof (111 identities), `independent_check.py` | Descent2R (505 modules), T1Zero, Bridge, Combine |
| Numerical elimination | Four paper certificates; 35-minor span; char-0 transfer; `a816_full.sing` and the explicit a₈,₁₆ certificate (`scripts/a816_certificate/`, two exact checkers) | Step-1 certificates (exact K₅ slice + 3 modular); rank lemma + two-prime ranks |
| Controls | 14/14 (3 ACCEPT, 9 REJECT, 2 sorry-flagged) | T1Zero 5 negative controls; rank planted-zero control; step-1 perturbed/dropped controls |
| External review | HLRE v5.0 audit + errata (`audits/`) | (deferred: p-adic argument; correspondence guide) |

---

## 7. Reproduction

### Branches (a,b)

```bash
cd branches_a_b
bash verify_v19.sh                      # checksums, scripts, 111/111 identities, 2026-10-05 checks, paper build
cd lean
lake exe cache get
LEAN_NUM_THREADS=1 bash verify_branch_ab_lean.sh   # full build + 53-theorem axiom audit
```

### Branch (c)

```bash
cd branch_c
bash verify_branch_c.sh                 # -> bundle_v3_1/jacobian_lean/verify_branch_c_lean.sh
```

Requires elan/lake (Lean 4.34.0, Mathlib v4.34.0), python3 with python-flint and
sympy. Single modules peak at ~5.6 GB RSS; allow 12+ GB or set `LOWMEM=1`.
Step 0 fingerprints the branch-(a,b) prerequisites, so the (a,b) Lean tree must
be present underneath `jacobian_lean/` (see GUIDE.md §12 for the overlay procedure).

---

## 8. Provenance and version history

- **Branches (a,b):** v17 (2026-09-28) → v18 (build fixes, wording) → v19
  (independent blind review: no fatal flaw; ten recommendations implemented).
  Published: Zenodo 10.5281/zenodo.23023490. The v17/v18 trees are preserved on
  repo main as `branch_ab_v17/`, `branch_ab_v18/` until 2026-09-30, when both were removed and `branch_ab_v19/` renamed to `branch_ab/`.
  - 2026-10-03: `branch_ab_v19/` was restored at the repository root as a copy of `branches_a_b/`, because the
    Zenodo record cites that path.
  - 2026-10-05: the a₈,₁₆ certificate, the Lean m = 3, 5 classifications (`Jacobian/B26`) and the B2.2 resolution
    were added (PR #3), followed by the check of CAIC's B2.6 data file. `branch_ab_v19/` was synced to stay
    byte-identical with `branches_a_b/`. See `branches_a_b/CHANGES_v19.md` §15.
- **Branch (c):** the `branch_c/` pipeline scripts on repo main (corrected
  2026-09-29: E₁ projection, 6d κ=0, Singular hang guard) → v2 bundle → v3.0
  (bundled mid-build) → **v3.1** (2026-09-29, 23:40 CDT; every module built,
  `verify_branch_c_lean.sh` passed, `Bridge` bug found and fixed). The v2
  corrected-commit proposal is **not** applied. See `branch_c/V3_1_PROVENANCE.md`.
- **This unified directory** (2026-09-30): `branches_a_b/` is `branch_ab` (v19) byte-for-byte; `branch_c/bundle_v3_1/` is the v3.1 bundle byte-for-byte
  (manifest-verified at assembly). New: this map, the READMEs, `BUILD_STATUS.md`,
  checksums, `verify_branch_c.sh`, and the conditional correspondence-guide to-do.

## 9. Deferred and open items

1. **Branch-(c) correspondence guide** — conditional to-do, NOT started:
   `TODO_correspondence_guide.md`. Created only after the finalized paper is drafted.
2. The p-adic argument for branch (c) — review deferred.
3. The branch-(c) `.tex` elimination paper — **done 2026-09-30**:
   `branch_c/paper/branch_c_elimination.tex` / `.pdf` (16 pages, Noto Sans /
   Noto Sans Math); `BRANCH_C_GUIDE.md` remains the comprehensive reference.
4. `ChartEmptyC_T1ne0` in Lean — currently outside Lean (grade B); formalizing the
   rank lemma's instance in Lean is listed as optional (GUIDE.md §11).
5. Branch-(c) figures — none produced yet.
6. GGHV Prop. 4.3's other cases and the reduction from the Jacobian conjecture —
   outside scope, unchanged.
