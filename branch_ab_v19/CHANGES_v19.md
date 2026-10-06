# v19 changes vs v18 (commit 42cbf03)

This tree is `branch_ab_v19/`; the v18 tree (commit 42cbf03, pushed
2026-09-28) is preserved as `branch_ab_v18/`. v19 implements the ten
recommendations of the independent final blind review received 2026-09-28,
which found no fatal flaw in the b_{12,24}=0 chain and judged v18
"mathematically serious and potentially publishable ... Close, but I would
revise before submission."

Two-commit publication scheme: the artifact commit freezes the executable
artifacts (scripts, Lean sources, logs, machine-readable certificate);
a second metadata commit replaces the `V19COMMIT` placeholder in the paper
with the artifact commit's hash and recompiles the PDF. The paper's
reproducibility appendix names the artifact commit.

## 1. Paper — title, theorem hierarchy, terminology
- `branch_ab_v19/paper/branch_ab_elimination_v3.tex` (and recompiled `.pdf`,
  now 31 pages)
- Title tightened to "Elimination of the GGHV Branch-(a,b) Normal Form at
  Degree Pair (72,108): A Certified Computational Audit", naming the GGHV
  normal form and no longer implying the whole (72,108) case is solved.
- Theorem 1.1 (main theorem) now concludes only b_{12,24}=0, which alone
  contradicts NewtonNF2; a_{8,16}=0 is demoted to Corollary 1.2, an
  independent exact-computer-algebra lower-edge rigidity result
  (`a816_full.sing`), not part of the Lean formalization.
- "Unconditional kernel-checked theorem" replaced by "kernel-checked
  theorem independent of GGHV Proposition 4.3" everywhere, except
  "unconditionally solvable" which refers specifically to E3.
- Abstract, outline, and a dependency table now state exactly which results
  depend on GGHV Proposition 4.3 (only Corollary 1.4, the Jacobian
  application) and which do not.

## 2. Paper — four certificates and obstruction-theoretic framing
- The proof is reorganized around four certificates: I (Newton/layer
  reduction), II (top-layer completeness), III (descent obstruction),
  IV (vertex destruction); a_8,16=0 is a supplementary rigidity result.
- New Remark (obstruction theory): the five top-layer orbits exist, but none
  admits a compatible lower-layer deformation — the E2 compatibility minors
  generate (t1,t2)^5, so the deformation cone is {0}.
- The Newton filtration interpretation is stated explicitly in the layer
  reduction: the five E_i are the homogeneous components of [P,Q]=x^2 with respect to the Y-weight grading.

## 3. Paper — new lemmas and explicit arguments
- Lemma (characteristic-zero transfer): every F-valued solution of the
  normalized m=7 chart system (F of characteristic 0) is a specialization
  of one of the five K5-solutions at a root w in F of R.
- Lemma (universal residue field): R is irreducible and separable over Q,
  so K5 is a number field; exact rank/ideal identities over K5 persist under
  every characteristic-zero field extension.
- Remark (Lean-to-mathematics correspondence): the Lean predicate NewtonNF2
  is exactly the support conditions of Theorem 1.1 plus nonvanishing of the
  eight vertex coefficients; the half-plane predicates are tied to the
  vertex sets by `decide` (25 and 47 lattice points).
- Remark (roles of the two classifications): Belyi gives the geometric upper
  bound (at most 35 chart points); the algebraic certificate gives the
  actual characteristic-zero classification. The main theorem uses only
  the latter.
- The 35-minor span argument is now fully explicit in the proof of the
  no-nonzero-direction theorem: rank 6 of the 35x6 coefficient matrix gives
  span = K5[t1,t2]_5, hence (t1,t2)^5 ⊆ I ⊆ (t1,t2)^5, so I=(t1,t2)^5.
- The t=0 collapse is promoted to a displayed lemma
  (t=0 ⇒ A1=B2=0 ⇒ 2A2B0'=0 ⇒ B0'=0 ⇒ b_{12,24}=0).
- The 35/5/1 decomposition (35 a6-solutions → 5 S-solutions → 1 Galois
  orbit) is displayed explicitly.

## 4. Paper — attribution and disclosure
- The independent Claude replication is reframed as an "independent
  AI-assisted computational audit" (evidential weight on the reproduced
  artifacts, not on the identity of the auditing system), not "scientific
  validation by another AI".
- The AI-usage paragraph moved from §11 (attribution) to a new appendix
  section "Computational and AI-assisted research disclosure".

## 5. Paper — reproducibility statement
- The computational-archive appendix now carries a reproducibility
  statement: repository URL, branch_ab_v19/ directory, artifact commit
  hash, Lean 4.34.0 (`lean/lean-toolchain`), `lake build`, `#print axioms`
  on `main_theorem` (propext, Classical.choice, Quot.sound), the
  generator→certificate→theorem chain, and the machine-readable
  K5 certificate (item 6).

## 6. Machine-readable K5 minor certificate
- `branch_ab_v19/scripts/exact_obstruction_K5.py` — new section 4b: after
  computing the 35x6 coefficient matrix and its rank, the script writes
  `logs/k5_minor_certificate.json` containing the field defining
  polynomial, the ordered binary-quintic monomial basis, the full 35x6
  matrix over K5 (each entry as 5 rationals), the rank (6), the pivot row
  indices of one explicit 6x6 nonzero minor ([0,1,2,3,5,6]), and that
  minor's determinant in the K5 basis. An independent checker needs only
  K5 arithmetic to confirm rank 6. Verified: exit 0; the JSON is
  byte-identical across runs (MD5 4ead0d7b36f38bddac4952469a15d5c6).
- `branch_ab_v19/logs/k5_minor_certificate.json` (new) — the certificate.
- `branch_ab_v19/logs/v19_scripts.log` (new) — recorded stdout and exit
  codes (all 0) of belyi_counts_m357.py, exact_ranks_K5.py,
  exact_obstruction_K5.py, and independent_check.py (111/111).

## 7. One-command verification script
- `branch_ab_v19/verify_v19.sh` (new, executable) — runs checksum
  verification, the three exact scripts, the 111/111 independent check,
  and the paper recompile, recording every command and exit code.

## 8. Documentation
- `branch_ab_v19/scripts/README.md` — documents the certificate dump.
- `branch_ab_v19/README.md` — v19 header (31 pages, four certificates,
  kernel-checked theorem independent of GGHV Proposition 4.3).
- `branch_ab_v19/BUILD_STATUS.md` — v19 packaging note added.
- `branch_ab_v19/CHECKSUMS.md5`, `CHECKSUMS.sha256` — regenerated for the
  v19 bundle subset.
- `branch_ab_v19/paper/branch_ab_elimination_v3.{aux,log,toc,out}` —
  recompile byproducts of the v19 paper (31 pages, xelatex exit 0, no
  undefined references, no overfull boxes).

## 9. Verification
- Exact change: `diff -r branch_ab_v18 branch_ab_v19` (excluding `.lake/`,
  `__pycache__/`, and the regenerated checksums).
- Paper: xelatex exit 0, 31 pages, no errors, no undefined references, no
  overfull boxes.
- Scripts: belyi_counts_m357.py, exact_ranks_K5.py,
  exact_obstruction_K5.py all exit 0; independent_check.py 111/111 PASS.
- Lean: `lake build` under Lean 4.34.0 (see BUILD_STATUS.md for the build
  record); `#print axioms` on `main_theorem` reports only propext,
  Classical.choice, Quot.sound.
- Manifest: all entries verify under MD5 and SHA-256 (see the verification record in BUILD_STATUS.md).

## 10. Post-v19 reviewer fixes (commits a633e17, fcbc917, 2529293, and this one)
- `a633e17`: paper wording — independent_check.py scope note ("verifies the arithmetic of the certificates only; it does not re-prove the mathematical statements"); BUILD_STATUS.md Lean build record.
- `fcbc917`: rebuilt PDF from the a633e17 source (31pp, xelatex exit 0).
- `2529293`: reviewer findings 1–6 — all 9 .sh files set executable (100755); abstract + Remark 6.7 classification wording ("proved twice"); §4 grading terminology; dependency diagram; Lemma 9.1 proof added; smaller items (Thm 6.3, Lemma 6.6, Thm 8.3, Remark 8.4, title, Remark 1.3, reproducibility, Appendix C, §11).
- This commit: Lemma 9.1 irreducibility via mod-67 (replaces false Eisenstein claim); verify_v19.sh compiles paper in temp dir (no longer mutates tree); checksums regenerated; Remark 6.7 "m=7 case"; Lemma 8.5 wording; Thm 8.3 proof notation; reproducibility stale-build note removed.

## 11. verify_v19.sh Python portability (this commit)
- `PY="${PYTHON:-python3}"`: caller can override interpreter (e.g. `PYTHON=/path/to/physics/bin/python ./verify_v19.sh`).
- Flint availability checked at start with clear error message.
- Page-count read from xelatex log via grep (no pdfinfo/poppler dependency).
- Removed committed `__pycache__/` files (were force-added despite .gitignore).

## 12. Lemma 6.6 polish + PDF rebuild (this commit)
- Lemma 6.6: "its five specializations at the five roots of R (over a splitting field of R)".
- PDF rebuilt with permanent TeX Live installation (~/texlive): 31 pages, 0 errors, 0 undefined references.

## 13. Lemma 9.2 Remark 9.3 citation + Remark title fix (this commit)
- Lemma 9.2 proof: "(the S = a6^7 parametrization; Remark~\ref{rem:import})" — cites the derivation remark for K5 ≅ Q(rho^7).
- Remark 9.3 title: "$W$" -> "$\mathcal{W}$" (eliminant, not the §7.3 matrix).
- PDF rebuilt: 31pp, 0 errors, 0 undefined refs, 0 overfull boxes.

## 14. Reproducibility paragraph cites final commit (this commit)
- Reproducibility paragraph: commit hash 9b7d541 -> 7597700 (the first commit where scripts, permissions, and checksums are all final).
- PDF rebuilt: 31pp, 0 errors, 0 undefined refs.

## 15. 2026-10-05: a₈,₁₆ certificate, m = 3, 5 classifications in Lean, B2.2 resolution (branch `claude/a816-b26-b22-resolution`)

### `scripts/a816_certificate/`
- **What 3304df0 left out.** That commit added only `README.md`, `SHA256SUMS`, `a816_lift.txt` and `verify_bundle.sh`,
  so `verify_bundle.sh` could not run.
- **Completed.** Added the generator (`structured_cert.py`), both independent checkers (`verify_cert_flint.py` and the
  Singular scripts), the negative controls, the multimodular route, CAIC's inputs and the logs.
- **Paths.** The scripts now read `../a816_full.sing` (or the identical copy here, md5 `aa68d2ff…`) instead of an
  absolute path.
- **Not committed.** `a816_lift_liftstd.txt` (36.4 MB, sha256 `dd9082fd…`). `verify_bundle.sh` checks it when present.
- **Result.** `verify_bundle.sh` passes in the repository (`logs/verify_bundle_repo.log`).

### `lean/Jacobian/B26.lean` and `lean/Jacobian/B26/` (10 modules)
- **Replaced.** The 2b6d208 skeleton is gone. Its statements were over `ℚ`, where `T₅` has no root, so they were
  vacuous; `QQ` is undefined, so the file did not compile; and it was not imported.
- **New theorems** (namespace `BranchAb.TopLayerSmall`, any field of characteristic 0):
  - `m5_chart_iff`: the m = 5 chart system of `E₅` holds iff `T₅(a₄) = 0`, the three back-substitution relations hold,
    and `b₁…b₇` are explicit polynomials;
  - `m5_residual_iff`: an ideal equality, both inclusions certified;
  - `m5_T_squarefree`, `m5_a4_ne_zero`, `m5_solution_formulas`;
  - the same for m = 3.
- **Checks.** No `sorry`, no warnings; standard axioms only.
- **Wiring.** Imported by `Jacobian.lean`, and listed in `AxiomsAudit.lean` and `verify_branch_ab_lean.sh`.
- **Generator, certificates, logs.** In `scripts/b26_m5_eliminant/lean_certificates/`; `regen_b26.sh` regenerates
  the files byte-identically.
- **Build.** A clean build is recorded in `logs/build_modules_seq.log`. The largest module, `M5T`, needs 3.8 GB.
- **Independent check of the statements.** `independent_checks.py` does not use the generator.
  - It parses `m5Chart` and `m3Chart` from the Lean source and confirms that they are exactly $E_1..E_{n+m}$.
  - It reads $T$ and the relations from `m5_chart_iff` and `m3_chart_iff`, and confirms the 10 and 3 distinct
    solutions to 60 digits.
  - Each check also runs on a perturbed input, where it must fail.
  - It runs in `verify_v19.sh` step 4b.
- **Scope statements updated.** "m = 3, 5 are not formalized" no longer holds. These now say the cases are formalized
  separately and are not used by the main theorem:
  - `README.md`;
  - `lean/CLASSIFICATION_STATUS.md`;
  - `lean/certgen/chartproof/README_chartproof.md`;
  - `correspondence_guide/CORRESPONDENCE_GUIDE.md`.

  The dated v17 note in `BUILD_STATUS.md` is left as written.

### `scripts/b22_structured/`
- **New files.** `RESOLUTION.md`, `b22_validate.py` (with `b22_validate.log` and `b22_s_point.json`), and a copy of
  `k5.py`.
- **Finding.** B2.2 is the Lean chart system `ChartClassification`. The exact K₅ point solves the c-recursion system,
  and `s = c₁₀/a₇ ∈ K₅`. The reduced 7×7 system needs `a₇ ≠ 0`.
- **Correction notes.** Prepended to `DERIVATION_REPORT.md` and `computational_20261004/b22_structured/B22_structured.md`.
- **Output location.** `b22_validate.py` writes `b22_s_point.json` next to itself, so `verify_v19.sh`, which calls it
  from `lean/certgen/`, leaves no stray file.

### `colab_a816/README.md`
- **Annotation of the archived notebook** `a816_lift_attempts_2026-10-04.ipynb`, added on main in 91c8ff7, which this
  branch is based on.
  - The run in characteristic 0 reached `G[1]=1` and was then stopped during `lift` at the 2-hour limit.
  - The run that finished used the ring `(32003,w)`. R factors mod 32003 with degrees 1, 1, 3, so that quotient is
    not a field. Its output, a Colab-only file also called `a816_lift.txt`, is a modular computation and not the
    certificate.

### `computational_20261004/`
- **`a816_lift/README.md`, `a816_lift/a816_simplified.md`: correction notes.**
  - 1,000,003 and 32,003 are not inert primes for `R`, so the "F_{p⁵}" statements are wrong.
  - `std` over Q(w) takes 7.8 s here.
  - The exact certificate exists.
- **`b26_m5/B26_m5_complete.md`: update note.** Completeness is now certified, and the result is in Lean.

### Paper (`paper/branch_ab_elimination_v3.tex`)
- **Corollary `cor:a816`.** The statement now cites the certificate. The proof gives the identity and the layer
  structure: ranks 17, 18, 12; free unknowns τ, σ; the 14 depth-4 monomials.
- **New Remark `rem:full-rigidity`.** The span statement implies that all 51 unknowns, the non-constant lower
  coefficients, vanish at the K₅ point. It is stated with its verification status, and is not used elsewhere.
- **Other text edits.**
  - `rem:conditional` wording;
  - the vertex-conditions paragraph;
  - the Proposition `prop:top-class` proof (Lean for m = 3, 5);
  - the characteristic-0 core;
  - reproducibility;
  - the AI disclosure, covering Claude's and Muse/CAIC's 2026-10-04/05 contributions.
- **Layout fix.** Remark 6.2's Lean path is now `\filename`, so it can break; this fixes a pre-existing 101 pt
  overfull box.
- **PDF rebuilt.**
  - Toolchain: TeX Live 2026 (TinyTeX, xdvipdfmx 20260317), with the Fira Sans, Mono and Math fonts from CTAN.
  - Result: 33 pages, 3 passes all exit 0, 0 errors, 0 undefined references, 0 overfull boxes.
  - The previously committed PDF has 32 pages (built 2026-10-01 from e8e1d8c), and the same toolchain reproduces
    32 pages from that source.
  - The committed `.log` that reported 31 pages was stale.
  - 0957290 changed the `.tex` without rebuilding the PDF.

### Verification files
- **`verify_v19.sh`.** New step 4b runs `verify_bundle.sh`, `regen_b26.sh`, `b22_validate.py` and
  `independent_checks.py`. The expected page count is now 33.
- **`scripts/README.md`.** New entries and attribution.
- **Checksums.** `CHECKSUMS.md5`, `CHECKSUMS.sha256` and `lean/MD5SUMS` were regenerated, with the same coverage
  rules. They now include the 2026-10-04/05 additions.

### After PR #3 was merged: `scripts/b26_m5_eliminant/B26_EXPLICIT_DATA.md` (CAIC, 12c6034)
- **Checked.** `check_explicit_data.py` compares every entry with the repository, and all are correct:
  - r0..r3 equal the `.sing` residuals and Lean `m5r0`..`m5r3`;
  - G1..G10 equal Singular's `std` output (not reduced);
  - the ideal equality holds; vdim = 10; the elimination ideal is (T);
  - det 30408 a4^3, the back-substitution, and both discriminants are right;
  - one negative control is rejected.
- **Note appended to the file.** It gives the reduced basis and says which three elements form the linear system
  with determinant 30408 a4^3.
- **Wiring.** `verify_v19.sh` step 4b runs the check. The checksums now cover the file.

### Same follow-up: `branch_ab_v19/` synced, a Lean verifier fix, the paper's revision date
- **`branch_ab_v19/` synced.**
  - That directory, at the repository root, is the path that the Zenodo record 10.5281/zenodo.23023490 cites. It was
    restored on 2026-10-03 as a copy of this package.
  - It is now again byte-identical to `JC2D-branches_a_b_c_unified/branches_a_b/`.
  - This means it now includes everything from 2026-10-04/05, so the published path shows the current results.
- **Fix to `lean/verify_branch_ab_lean.sh`, a defect introduced in PR #3.**
  - Step 3 counted only theorems whose axioms are exactly `[propext, Classical.choice, Quot.sound]`.
  - `m5_a4_ne_zero` and `m3_a2_ne_zero` use only `propext` and `Quot.sound`, so a full run would have reported
    "51 of 53" and failed.
  - The check now accepts any subset of the three standard axioms and still rejects any other axiom. It was tested on
    the real output for all 53 theorems, which passes, and on a control with an injected non-standard axiom, which is
    rejected.
  - The output is in `lean/logs/axioms_verify_script_53.log`.
  - The theorem count in `README.md`, `lean/README.md` and the script header is now 53.
- **Paper.**
  - The date line reads "September 28, 2026; revised October 5, 2026".
  - The reproducibility paragraph names both copies and keeps commit 7597700 for the first v19 release. It lists the
    revision's additions and states exactly which Lean files changed.
  - PDF rebuilt: 33 pages, 0 errors, 0 undefined references, 0 overfull boxes. The 3 underfull boxes were already
    there. The abstract is unchanged.
- **Other docs.** `README.md` now notes the two identical copies. The stale line "v18 tree preserved as
  `branch_ab_v18/`" is corrected; that tree was removed on 2026-09-30 and is still in the git history at 42cbf03.

### 2026-10-06: the abstract, the solution counts in Lean, the branch-(c) status
- **Abstract.**
  - A new paragraph states the m = 3, 5 results. In Lean the chart system holds iff $T=0$ and the other unknowns take
    explicit values; the eliminant has no repeated root; the exact counts 3 and 10 are kernel-checked; and
    Theorem 1.1 does not need these cases.
  - The sentence on $a_{8,16}=0$ now names the explicit certificate $a_{8,16}^2=\sum_k H_ke_k$ over $K_5$, checked
    exactly by two independent programs, and states that it is not part of the Lean formalization.
- **`lean/Jacobian/B26Count.lean` (new, hand-written).** It proves `m5_chart_card` and `m3_chart_card`: over every
  algebraically closed field of characteristic 0 there are exactly 10 (resp. 3) chart solutions.
  - Proof: a bijection with the roots of T (`m5_chart_iff`, `m3_chart_iff`), separability of T over ℚ by an explicit
    Bézout identity, and natDegree, then Mathlib's `card_rootSet_eq_natDegree`.
  - Standard axioms only.
  - It is imported by `Jacobian.lean`, and listed in `AxiomsAudit.lean` (now 24 declarations) and in
    `verify_branch_ab_lean.sh` (now 55 theorems).
  - The file is placed outside `Jacobian/B26/`, so that `regen_b26.sh` still compares only generated files.
- **Generated docstring.** The generator's text in `B26.lean` ("the count … is not restated as a separate Lean
  theorem") now points to `B26Count.lean`. `regen_b26.sh` still regenerates byte-identically.
- **Paper.** The proof of Proposition 6.1 cites `m3_chart_card` and `m5_chart_card`, and the reproducibility list
  includes `B26Count.lean`. 33 pages, 0 errors, 0 undefined references, 0 overfull boxes.
- **Logs.**
  - `lean/logs/b26count_build_and_axioms.log` (new).
  - `lean/logs/axioms_verify_script_55.log` (new; the 53-theorem log is kept).
  - `lean/logs/axioms_audit_with_B26.log` (24 declarations).
- **Branch (c), outside this package.**
  - The v2 corrected-commit proposal was in fact applied to main as `2b77cd4` on 2026-09-29; the result is
    byte-identical to `proposed_branch_c/`. The top-level `branch_c/` was later removed (`d65a007`, 2026-10-01).
  - The statements "not applied" in `branch_c/BUILD_STATUS.md`, `branch_c/V3_1_PROVENANCE.md` and `TECHNICAL_MAP.md`
    are corrected. `GUIDE.md` is a byte-for-byte copy of the bundle's guide and is left unchanged.
