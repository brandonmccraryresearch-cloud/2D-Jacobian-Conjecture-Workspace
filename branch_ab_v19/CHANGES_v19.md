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
  reduction: the five E_i are the associated graded components of [P,Q]=x^2.

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
- Manifest: all entries verify under MD5 and SHA-256 (see §10 of this
  file's verification record in BUILD_STATUS.md).
