# Review of the work done between 2026-10-08 and 2026-10-12

**Reviewer.** Claude (Anthropic), working for Brandon D. McCrary. **Date.** 2026-10-12.
**Branch.** `claude/review-handoff-2026-10-12` (from `main` at `3e7c180`). Nothing in this review was published,
deposited, uploaded or minted.

**Scope.**
- Merged on `main`: PR #12 (root replication package), PR #13 (branch-(c) correspondence guide), PR #14
  (`verify_v19.sh` page count), PR #15 (route C, `lean/Jacobian/A816C`).
- Not merged: the branch `caic/branch-c-cleanup` (the A1–A5 Lean drafts and the "I3 complete" documentation).
- Handed over in `claude_handoff_2026-10-12_2.zip` and not in the repository: the I3 implementation, the
  two-dicritical Lean files, the progress changelog, and the unsent e-mail draft to C. Valqui.

**Method.** Every claim below was re-run or re-derived; nothing is taken from the authors' own reports. The tools:
Lean 4.34.0 with Mathlib v4.34.0, Python 3.11.15 with sympy 1.14.0 and python-flint 0.9.0, Singular 4.3.2,
PARI/GP 2.15.4, TeX Live 2026 (TinyTeX). The grades are the project's: **A** = Lean kernel, standard axioms only;
**B** = exact computation outside Lean; **C** = evidence. Independence levels I0–I4 are HLRE's.

---

## 1. Verdicts

| # | Item | Verdict | Severity | Done in this branch |
|---|---|---|---|---|
| 1 | PR #14: `verify_v19.sh` expects 35 pages | **Wrong.** The shipped PDF has 34 pages and the current source builds to 34. The PR also did not regenerate the manifests, so `main` fails its own verification (`PASS=15 FAIL=3`). | High: the one-command check of the published package is red | Fixed (34, with 35 accepted); manifests regenerated; `PASS=18 FAIL=0` |
| 2 | PR #15: route C | **The Lean is sound** (builds, standard axioms). **The integration is not:** files in one of the two copies only, not in any manifest, not in any verify script, no generator, no statement check, no README; its "control" C7 is not a perturbation control. | Medium | Integrated: copied, statement check written (PASS, 3 controls), `verify_routeC.sh`, README §1d, manifests |
| 3 | PR #12: root "blind" replication guide, key, comparator | **Mislabeled and partly wrong.** It re-runs the project's scripts, which print their expected values: a reproduction (I1), not a blind replication. Its I3 path leaks the expected values. Four key values are wrong (A1, A2, A10, C2). | Medium | Renamed `REPRODUCTION_*`; corrected; the blind guide is `replication/` |
| 4 | PR #13: branch-(c) correspondence guide | **Section mapping wrong** for §§3–8; it omits a contradiction in the paper (§6 "Formalization seam" vs. §5 B2 and the Lean files). | Medium | Mapping corrected; the paper's discrepancy recorded (the paper itself is not changed here) |
| 5 | I3 replication (CAIC, 2026-10-11) | **Numbers correct, independence overstated.** Internal agent, and the specification it worked from states the expected values. I1–I2, not I3. | Medium (a false independence claim) | Recorded; claims on `caic/branch-c-cleanup` not accepted |
| 6 | A1–A5 Lean drafts (`caic/branch-c-cleanup`) | **Not a path to grade A as written.** A4 and A5 are vacuous (stated over ℤ, where R has no root; Lean witness). A5 assembles the claim from an axiom that is the claim, plus axioms `: True`. A3's transfer lemma cannot be applied (no ring map from a characteristic-0 field to 𝔽_p). A2 is stubs. A1 is genuine but has 3 `sorry`s and no link to the kernel-checked data. | High for any merge | Not merged; a corrected architecture is in §4 |
| 7 | Two-dicritical Lean (handoff only) | **`Bridge.lean`'s two axioms are false as stated** (Lean witness), so its theorems are vacuous. It does not compile under Lean 4.34. `BlockRank.lean` and `E1Obstruction.lean` compile with standard axioms. | High for any claim built on `Bridge` | Witness added; repair route in §5.2 |
| 8 | Two-dicritical paper | **"Closes that line completely" is not supported.** The adjacent case is computed at d = 3 only; the constant-leading-form proposition has a proof sketch. | High for the paper's main claim | Recorded |
| 9 | E-mail draft to C. Valqui (unsent) | **Overclaims** ("fully verified", "proved twice independently in Lean 4 ... with negative controls"). | High if sent as is | Recorded; nothing sent |

Things that are right and stay as they are: the route-C kernel proofs; `BlockRank.lean`; `E1Obstruction.lean`; CAIC's
`IrreducibleR.lean` up to one `sorry` (closeable, §4.4); A1's digit argument; the I3 implementation's numbers; the
answer-key values A3–A8 and C1, C3, C4 of PR #12.

---

## 2. Defects on `main`, and their fixes

### 2.1 PR #14: the page count, and the manifests

**Claim of the PR.** "PR #11 added a page"; the paper builds to 35 pages; `verify_v19.sh` should expect 35.

**Evidence.**
- `branches_a_b/CHANGES_v19.md` §16 (written with PR #11): "PDF: 34 pages (was 33)". PR #11 took the paper from 33
  to 34 pages, not to 35.
- The shipped `paper/branch_ab_elimination_v3.pdf` has 34 pages (`pdfinfo`).
- A build of the current source with TeX Live 2026 (TinyTeX) and the CTAN Fira fonts, three `xelatex` passes, gives
  34 pages and 0 missing glyphs.
- One other TeX Live 2026 installation gave 35 pages (CAIC, 2026-10-08). Line breaking depends on the installation.
- PR #14 changed `verify_v19.sh` in both copies but did not regenerate `CHECKSUMS.md5` / `CHECKSUMS.sha256`. On `main`
  both manifest checks fail on that one file. `reviews/logs/verify_v19_main_3e7c180.log`: `PASS=15 FAIL=3`
  (md5, sha256, page count).

**Fix.** `verify_v19.sh` accepts 34 (the shipped PDF) or 35 (the known variant) and fails on anything else; the
reason is written in the script. Manifests regenerated (478 entries: the 418 old ones and 60 new files).
`reviews/logs/verify_v19_this_branch.log`: `PASS=18 FAIL=0`, 79 s.

### 2.2 PR #15: route C

**What it is.** `lean/Jacobian/A816C/` (55 files): `A816C.routeC_a816` derives `a₈,₁₆ = 0` from the 75 bracket
equations of weights 3…0 at the K₅ top layer, along the certificate's own pivot chain (`Pivot/P01–P47`, `Final`),
independently of `Jacobian/Descent`; `A816C.Bridge.routeC_source` restates it for the source variables.

**Checked here.**
- **Build:** exit 0 in 2020 s on 2 cores; 819 warnings, all cosmetic (763 unused section variables, 37
  deprecations, 19 unused hypotheses) (`lean/logs/routeC_build.log`).
- **Axioms:** `[propext, Classical.choice, Quot.sound]` for `routeC_a816`, `routeC_source`, `transfer` and the C7
  theorem (`lean/logs/routeC_axioms.log`).
- **The 19 unused hypotheses** are 1, 1, 1 and 16 equations of weights 3, 2, 1, 0. So 17, 18, 18, 3 equations are
  used, the same counts as the certificate's nonzero cofactors. Expected, not a defect.

**Defects.**
1. The files were added to `branch_ab_v19/` only. The two copies of the package must be byte-identical; they no
   longer were.
2. No manifest lists them, and no verification script builds them (`Jacobian.lean` does not import them).
3. **The generator `routec_gen.py` is not in the repository**, although the files say "generated by routec_gen.py".
4. **Nothing checked that the hypotheses mean what they should.** `routeC_source` is a statement about reflected
   expressions `G_i_j`. That these are the bracket equations of P and Q was asserted, not checked.
5. `C7_transfer_fails_without_divCtx` was presented as a negative control. It shows that the substitution identity
   fails without the rescaling `divCtx`, a property of the bridge. No perturbed copy of a certificate identity was run
   against the kernel.
6. It is reflection-level: no theorem connects `routeC_source` to `jac P Q` for `MvPolynomial`s.

**Fixes.**
- The 55 files copied into `branches_a_b/`; the two copies are byte-identical again (equal tree ids).
- **New statement check** `lean/certgen/check_routeC_statement.py` (sympy; reads the Lean text and
  `scripts/a816_full.sing` only). With `var 0 = w` and `var k` the k-th unknown of `a816_full.sing`:
  - `eR` is R;
  - every `G_i_j` is a nonzero **integer** multiple (from 1 to 268736) of the coefficient of xⁱyʲ of
    J = P_x Q_y − P_y Q_x in K₅[unknowns];
  - the 75 labels are exactly the nonzero coefficients of weights 3, 2, 1, 0, none missing;
  - the conclusion is `(Expr.var 17).denote ctx = 0`, and var 17 is a₈,₁₆.

  Three controls (one integer changed; two variables swapped; one label dropped) each fail as required. Result:
  PASS, 22 s (`lean/logs/routeC_statement_check.log`).
- **New script** `lean/verify_routeC.sh`: build, axioms, statement check.
- **`lean/README.md` §1d** states what route C proves and what it does not.

**Grade after the fix.**
- The deduction "75 scalar equations ⇒ a₈,₁₆ = 0" along the certificate's route: **A** (kernel).
- Its identification with the bracket equations of P, Q: **B** (Python), Fidelity-Checked.
- Connection to `jac` in Lean: **none**. Route R (`lower_edge_rigidity`) remains the Lean proof at the level of P, Q.

### 2.3 PR #12: the root replication package

**Defects.**
1. **Not blind.** The guide asks the replicator to run `verify_v19.sh`, `run.sh` and the scripts, and only then to
   open the key. But the scripts print their own verdicts and many of the expected values: the page count,
   "covers = 1 (remainder 0)", ranks, "RESULT: PASS". What it tests is computational reproducibility with the same
   code: level I1.
2. **Its I3 path leaks.** §4.4 says to read `I3_REPLICATION_SPEC.md` §§1–7 first. Those sections state the expected
   values: §1 the size of M₂₄ and its full row rank, §3 the term counts, §4 the matrix sizes, §6 κ mod p, the test
   values, the nonzero count and the ranks.
3. **The comparator `answer_key_checks.py` contains every expected value** in its source, with no warning.
4. **Wrong key values:**
   - A1: "418 entries OK". On `main` both manifests failed (§2.1), and they omitted route C.
   - A2: "PASS=18". It was 15/3 on `main`. Also, 18 is the count only with Singular installed and without
     `lean/.lake`.
   - A10: "35 pages". The shipped PDF has 34 (§2.1). The guide's own §3.2 said 34.
   - C2: "rank mod 1000003: 3199" listed for the 3199 × 3199 block. Only M₂₄ (3199 × 6054) was ranked mod 1000003;
     the pivot block was never checked at that prime.
   - C2: "Negative control: exactly 1 bit flipped → rank drops". The controls are five kernel perturbations of one
     packed column (all rejected) and one positive control; none is a rank computation.
   - A9: "Exactly [propext, Classical.choice, Quot.sound]". Two of the 66 theorems use only `[propext, Quot.sound]`.

**Fixes.** Renamed `REPRODUCTION_GUIDE.md`, `REPRODUCTION_ANSWER_KEY.md` and `reproduction_key_checks.py`, and
corrected:
- §1 says what the protocol is (I1) and points to the blind guide;
- §4.4 no longer uses the specification;
- the comparator warns that it holds every value, and accepts 34 or 35 pages;
- A1 is now 478, and A2, A9, A10 and C2 are corrected, each with the reason.

The blind guide is `replication/INDEPENDENT_REPLICATION_GUIDE.md`, with a separate answer key recomputed in fresh
code. Its `run_key.sh` exits 0 in 201 s; 31/31 log checks pass. The key's SHA-256 is printed at the end of the guide,
so a replicator can check that it was not changed after they committed.

### 2.4 PR #13: the branch-(c) correspondence guide

**Defects.**
1. The paper's §4 is B0 + B4, §5 is B1–B3, §6 the top layer, §7 B5 (the paper's own table, §11). The guide put
   `chart_descent_refl` (B5) under §4, the 132-equation bridge (B4) under §5, `CondsC.lean` under §6, and chart
   scripts under §3.
2. **It omits a contradiction inside the paper.** The paragraph "Formalization seam" of §6 says that the degree-19
   rigidity lemma is not formalized in Lean, and that a classification argument behind it is grade B. The paper's
   own §5 (B2) and §11 (B1–B3, grade A) say the opposite, and the frozen bundle agrees with them:
   - `degree19_rigidity` (`Degree19.lean`), `vertex_12_24_forces_t2` and `edge19_rigidity_of_jac` (`Edge19.lean`)
     are Lean theorems with the three standard axioms (`bundle_v3_1/logs/verify_v3.log`);
   - `main_theorem_c_of_claim` uses `vertex_12_24_forces_t2` and `chartClassification_holds` directly
     (`DescentClaim.lean`, lines 165 and 169);
   - no branch-(c) Lean file mentions `e5_cert.json`.

   The seam paragraph cites an audit of 2026-09-26, the day before the branch-(a,b) classification was completed in
   Lean (v17). It appears to be out of date.

**Fixes.** The mapping is corrected section by section, and the discrepancy is recorded in the guide (§6 entry).
The paper is not edited here. Brandon or the paper's maintainer should replace the seam paragraph. Suggested text:
"An audit of 2026-09-26 flagged the degree-19 rigidity as a seam. It has since been closed: `degree19_rigidity`,
`vertex_12_24_forces_t2` and the branch-(a,b) classification `chartClassification_holds` are kernel-checked, and
`main_theorem_c_of_claim` uses them directly."

Also corrected: `branch_c/README.md` still called the guide "deferred", listed no figures and gave 16 pages; the
unified `README.md` and `TODO_correspondence_guide.md` were stale. The `branch_c/` manifests did not list the guide;
they are regenerated (1088 entries, same rule), and `bundle_v3_1/` is untouched (its manifest verifies).

---

## 3. The I3 replication (CAIC, 2026-10-11)

**What was done.** A Singular implementation built the weighted Macaulay matrices from `conds_c.json` and the
specification (`i3_replication/`). It found:
- ranks 2277/2278 (W = 22), 2707/2708 (W = 23) and 3199/3199 (W = 24) at p = 32003 and p = 1000003;
- 3198 for the planted-zero control.

**The numbers are right.**
- They agree with `step3b_rank_lift.log`, with `rank_lemma_check/`, and with the fresh code of
  `replication/answer_key/macaulay_rank.py`.
- The input fingerprint (`conds_c.json`: MD5 `168299d2…`, 1,782,507 bytes) checks.
- The rows are sorted so that e₁ is the monomial 1, as the specification requires.

**The independence claim is not right.**
- The implementer is an agent of the project, not an outside party.
- The specification it worked from states the target values: §1 states the size of M₂₄ and that it has full row
  rank; §6 gives every rank.

That is a re-implementation with known targets: **I1–I2**. The branch `caic/branch-c-cleanup` writes "I3
independent replication complete" and "This is the outside rebuild the spec called for" into `GUIDE.md`,
`README.md`, `BUILD_STATUS.md`, `paper/BRANCH_C_GUIDE.md` and `rank_lemma_check/README.md`. Those edits should not be
merged. The I3 item stays **open**; `replication/` is the guide for the outside party.

---

## 4. A1–A5 (`caic/branch-c-cleanup`, not merged)

### 4.1 Inventory, checked

| File | `sorry` | `axiom` | Finding |
|---|---|---|---|
| `a1_no_carry_bridge/NoCarryBridge.lean` | 3 | 0 | The packed-digit ("no carry") argument is genuine. Not linked to `RCCommon`'s Boolean checks or to the matrix `M_S`. |
| `a2_macaulay/Macaulay.lean` | 12 | 0 | Definitions are `sorry` stubs. The data correspondence (the crux) is not started. |
| `a3_irreducibility_transfer/IrreducibleR.lean` | 1 | 0 | Sound. The `sorry` is the degree case analysis (degree-1 factor → root; degree-2 factor → monic quadratic); both computational facts are proved. Closeable. |
| `a3_irreducibility_transfer/Transfer.lean` | 0 | 0 | Correct but **inapplicable**: `det_transfer_of_minor` needs a ring hom from the field K₅ to 𝔽_p, and there is none (characteristic 0 → p). |
| `a4_bezout_t1/BezoutT1.lean` | 3 | 0 | **Vacuous.** Stated over `Int`, where R has no root. |
| `a5_assembly/Assembly.lean` | 0 | 8 | **Circular.** `a4_chart_contradiction` is the claim itself, as an axiom; four axioms have type `True` or `True → True`. |

19 `sorry`s and 8 axioms in all, as CAIC's inventory says. The branch's `REGRADE.md` ("fidelity B+, I3") is not
supported by these files.

**Lean witness:** `reviews/lean/A4A5StatementsVacuous.lean` proves `R_no_int_root` (R has no root mod 67, hence none
in ℤ) and `vacuous_over_int : ∀ P, ∀ w : ℤ, R(w) = 0 → P`, both on the three standard axioms. Every A4/A5 statement
with the hypothesis R(w) = 0 over `Int` is an instance.

### 4.2 The target, restated

`ChartEmptyC_T1ne0 L` (`bundle_v3_1/.../T1Zero/Combine.lean`), for every field L with `CharZero L`:

$$\forall w\in L,\ R(w)=0\ \Rightarrow\ \forall\,t_1,t_2,s_1,s_2,r,u,q\in L,\ t_2=1,\ t_1\neq0,\ \Omega=\Psi=\Phi_{1,2}=\Theta_{1,2,3}=0,\ \text{pure rows}=0\ \Rightarrow\ \bot,$$

with t₁ = b₁₁,₂₀, t₂ = b₁₂,₂₂, s₁ = b₁₁,₂₁, s₂ = b₁₂,₂₃, r = a₆,₁₃, u = a₇,₁₅, q = b₁₀,₂₁. Over ℤ the statement is empty; the content
is that L may be any field of characteristic 0 containing a root of R.

### 4.3 A corrected architecture

**Step 1 (Ω).** `T1Zero.s_sq` gives Ω = o₁(w)·(s₂ − κ(w) t₂²)², and `T1Zero.s_X2` gives o₁(w) ≠ 0 by a Bézout
identity. With t₂ = 1 this forces s₂ = κ(w). Both lemmas are kernel-checked in the bundle and do not assume t₁ = 0.

**Step 2 (the six generators).** Substituting t₂ = 1 and s₂ = κ(w) into Ψ, Φ₁, Φ₂, Θ₁, Θ₂, Θ₃ gives
F_n(w; t, s, r, u, q). After clearing denominators, F_n ∈ ℤ[X][t, s, r, u, q] evaluated at X = w, with t = t₁ and
s = s₁.

**Step 3 (left kernel, no inverse needed over L).**
- Let z ∈ L⁵ be a common zero, and let v = (μ(z))_μ, indexed by the 3199 row monomials μ of weighted degree ≤ 24.
  Then v₁ = 1 (the monomial 1).
- For every column (n, m) of the Macaulay matrix M,

$$\sum_\mu v_\mu M_{\mu,(n,m)} = (m\,F_n)(z) = m(z)\,F_n(z) = 0,$$

  so vᵀM = 0, and in particular vᵀM_S = 0 for the 3199 pivot columns S.
- Since v ≠ 0, det M_S(w) = 0 in L.

  In Lean this is `MvPolynomial.eval` written as a sum over coefficients. M is defined symbolically as
  M_{μ,(n,m)} = coeff_μ(m·F_n); its 239,154 entries are never listed.

**Step 4 (the determinant as a polynomial).**
- D(X) := det M_S(X) ∈ ℤ[X] (`RingHom.map_det` for every evaluation).
- If D(w) = 0 then minpoly_ℚ(w) ∣ D in ℚ[X]. R is monic and irreducible over ℚ (§4.4), so minpoly_ℚ(w) = R
  (`minpoly.eq_of_irreducible_of_monic`) and R ∣ D in ℚ[X].
- R is monic, so the division is exact in ℤ[X]: `modByMonic` commutes with `map`, and ℤ[X] → ℚ[X] is injective.
  So D = R·Q with Q ∈ ℤ[X].
- Evaluate at w₀ = 11147 in 𝔽₃₂₀₀₃: D(w₀) = R(w₀)·Q(w₀) = 0.

**Step 5 (the kernel-checked inverse).**
- `rank_lemma_check/` has the kernel check C·M_S(w₀) ≡ I (mod 32003) in packed form.
- A1 turns the 6,398 packed identities into the matrix identity over `ZMod 32003`.
- Then det M_S(w₀) is a unit in 𝔽₃₂₀₀₃, against Step 4.

**What is new compared with the A1–A5 drafts.**
- The ring that carries the transfer is ℤ[X], with two evaluations, X ↦ w ∈ L and X ↦ w₀ ∈ 𝔽_p. A ring map
  K₅ → 𝔽_p does not exist.
- Everything is over L, never over ℤ.
- No inverse over K₅ and no ideal membership are needed; one determinant suffices.

**The hard part is Step 3's data correspondence (A2).** The kernel-checked data must be the evaluation at w₀ of the
symbolic M_S. There are two routes:
- **Prove it.** Entry by entry, about 10⁵ nonzero entries: heavy.
- **Avoid it.** Re-run the packed check with the columns of M_S computed inside the kernel from a sparse
  representation of F_n mod p, plus one soundness lemma linking the sparse form to `MvPolynomial` coefficients.

The second route reuses the existing check's design and should cost about as much kernel time (about 7 CPU-minutes).

### 4.4 Small pieces that can close now

- **R irreducible over ℚ in Lean:** CAIC's `IrreducibleR.lean` with its one `sorry` closed. This would make H3 grade A.
- **Steps 1, 4 and 5** are generic Lean (Mathlib lemmas named above) and do not depend on the 10⁵-entry data.

---

## 5. Two-dicritical material (handoff only)

### 5.1 Lean files

**Compile status.**
- `E1Obstruction.lean` and `BlockRank.lean` compile; their main theorems (`e1_degree_obstruction`,
  `not_keller_of_noLowTerms`, `block_rank`, `choose_det_ne_zero`) use the three standard axioms.
- `E1Obstruction` proves: if every monomial of P and Q has total degree ≥ 2, then [P,Q] has no constant term. Its
  link to the order condition ν_{E₁} ≥ −2 (the translation into "every monomial has J + K ≥ 2") is not formalized.
- `Bridge.lean` does not compile under Lean 4.34: the deprecated `∑ x in` syntax, and the section variable `hd`,
  which is used in proofs but not included.

**Bridge's axioms are false.** `Bridge.lean` declares `bridge_triangular` and `block_full_rank` after the section
variables `d`, `nEq` and `coeff`. Lean therefore quantifies each axiom over every system, not over the paper's
system:
- with every coefficient equal to 1, `bridge_triangular` is false, because the weight-0 variable (0,0) appears in a
  weight-2 equation;
- with no equations at all, `block_full_rank` is false.

Witness: `reviews/lean/BridgeAxiomsInconsistent.lean` (standard axioms). A copy of the original file with only its
syntax updated derived `False` from each axiom alone. So `step`, `bridge_vanish`, `nullspace_support` and
`keller_bridge_empty` are vacuous as they stand.

**Repair, and gaps (a)–(d) restated.**
- **(a) "Wire BlockRank into Bridge's axiom."** This cannot be done: the axiom is false. Instead, make both
  properties hypotheses of a structure about the paper's concrete system (its `coeff` from the pullback formula
  (4.1), its `nEq`). Then prove `full_rank` from `block_rank` for that `coeff`.
- **(b)** Prove `triangular` from the pullback formula for the concrete `coeff`.
- **(c)** The constant-leading-form step (m ≥ 2) is not formalized and has no complete paper proof (§5.2).
- **(d)** Assembly, after (a)–(c).

### 5.2 The paper (`branch_two_dicritical/paper/two_dicritical_closure.tex`)

- Line 81: "This paper closes that line completely."
- Lines 115–119: the constant-leading-form proposition, which carries the case m ≥ 2, has only a "Proof sketch".
- Line 217: "The adjacent case is closed by the d = 3 computation". The theorem is stated for all degrees, and no
  argument for d ≠ 3 is given.

As written, the main theorem is not proved. It holds at most for the bridge case at every d (by Corollary
cor:bridge-empty, which needs a sound Lean or paper proof of the bridge collapse, see §5.1) and for the adjacent case
at d = 3.

### 5.3 The e-mail draft to C. Valqui (unsent, in Brandon's Gmail)

It says the two-dicritical result is "Fully verified with 18 SymPy scripts". It says a₈,₁₆ = 0 is "proved twice
independently in Lean 4 — once via lower-edge rigidity ... and once via an ideal-membership certificate with negative
controls".

**Corrections.**
- §5.2 holds.
- Route C checks the certificate's structured route at the level of reflected expressions; it is linked to the
  bracket equations by a Python check (§2.2), not in Lean. It does not check the identity a₈,₁₆² = Σ H_k e_k. Its
  C7 theorem is not a negative control of the certificate.
- Route R is the Lean proof at the level of P, Q.

The branch-(a,b) and branch-(c) bullets are accurate if the last one says that `ChartEmptyC_T1ne0` is proved
outside Lean (grade B).

**Recommendation:** revise before sending.

---

## 6. What remains unproven or open

1. **Branch (c):** `ChartEmptyC_T1ne0` in Lean (grade B today). Status after this review:
   - plan §4.3 replaces A1–A5;
   - nothing of A2 exists;
   - A1 has 3 `sorry`s;
   - R's irreducibility has 1 `sorry` (closeable).
2. **I3:** no outside replication yet.
3. **Route C:**
   - no Lean link to `jac`;
   - no perturbation control;
   - the generator `routec_gen.py` is missing from the repository.
4. **Branch-(c) paper:** the §6 seam paragraph contradicts §5 and the Lean files; it is not yet corrected.
5. **Two-dicritical:**
   - Bridge must be rebuilt with hypotheses (gaps a, b);
   - m ≥ 2 has no complete proof (gap c);
   - the adjacent case is done only at d = 3;
   - so the main theorem is open.
6. **Out of scope throughout:** GGHV Prop. 4.3's other cases and the reduction to them. **Nothing here proves the
   Jacobian conjecture.**

---

## 7. Reproducing this review

```bash
# branch (a,b): the package's own check (18 steps with Singular; ~80 s)
cd JC2D-branches_a_b_c_unified/branches_a_b && bash verify_v19.sh
# route C: build (~34 min on 2 cores), axioms, statement check
cd lean && bash verify_routeC.sh
# the two review witnesses (any Lean 4.34 + Mathlib v4.34 project)
lake env lean ../../reviews/lean/A4A5StatementsVacuous.lean
lake env lean ../../reviews/lean/BridgeAxiomsInconsistent.lean
# the blind replication's answer key (~3.5 min; read the guide first)
cd ../../replication/answer_key && bash run_key.sh
# manifests
cd ../../branch_c && md5sum -c CHECKSUMS.md5 && (cd bundle_v3_1 && sha256sum -c MANIFEST.sha256)
```

---

## 8. Follow-ups opened the same day

- **PR #17** (stacked on this branch), `branch_c/grade_a/`: the generic half of `ChartEmptyC_T1ne0` in Lean.
  - R is irreducible over ℚ, so H3 is grade A.
  - The transfer through ℤ[X] (`eval_eq_zero_of_eval_root`, `no_left_kernel`).
  - The assembly `no_common_zero_of_certificate`.
  - What remains: the concrete generators, the rows and pivot columns, and A1/A2.
- **PR #18** (stacked on this branch), `branch_two_dicritical/lean/`: the bridge collapse proved from the paper's
  explicit equations, with no axioms. It also closes the W = 2 gap of the paper's proof.
- **`reviews/analysis/`**: the analysis of patterns across the eliminations (`DEEP_ANALYSIS_2026-10-12.md`). It
  includes a new observation: the top-layer cover counts are Catalan numbers for m = 3, …, 11
  (`belyi_catalan_counts.py`, with its log).

---

## 9. Second pass (2026-10-12, evening)

### 9.1 Where PRs #17 and #18 landed

- PR #16 was merged into `main` at 16:08 (`af1e860`; its tree is that of `78b3c2a`).
- PRs #17 and #18 were stacked on this review's branch. They were merged into that branch at 16:09 and 16:10
  (`4b05238`, `d6e4c4f`), after the branch itself had been merged.
- So GitHub shows them as merged, but `main` does not contain their 29 files.
- The branch `claude/bridge-premises-and-landing` starts at `d6e4c4f`. Its pull request into `main` therefore carries
  #17 and #18 unchanged (`grade_a/` is byte-identical to `4af460e`, `branch_two_dicritical/lean/` to `696e59d`)
  together with §9.3–9.4 below.

### 9.2 A cross-check of this review

Brandon relayed (16:17) a report by CAIC, which had re-checked PR #16 and confirmed its five load-bearing claims:
- `main` at `3e7c180` gives PASS=15 FAIL=3;
- PR #11 took the paper from 33 to 34 pages (the `.tex` blob has been `8c3e45a` in both copies since);
- the route-C statement check is genuine, controls included;
- the corrections to the answer key, C2 included;
- the two axioms of `Bridge.lean` are false, which CAIC accepts.

That is a second agent working on the same repository with the same tools (independence I1–I2), not an outside
replication.

On C2: CAIC's I3 run of 2026-10-11 ranked M₂₄ (3199 × 6054) modulo 1000003 (`i3_replication/REPRODUCE.md`), not
the pivot block M_S. So the statement "the pivot block was never checked at that prime" still holds.

### 9.3 The main theorem, as worded, is false

Theorem `thm:main` reads: "Let K be a field of characteristic 0 … with [P,Q] = c ∈ K^×. Then the resolution of the
pencil λP + μQ contains no two distinct dicritical divisors."

- **Every base point carries a dicritical.** Take a base point p. The exceptional curve over p is connected. If all
  of it lay in one fiber Φ = t₀ of Φ = P/Q, then a member with t ≠ t₀, which passes through p, would meet it.
- **Such a divisor is in every resolution.** A divisor on which Φ has non-constant residue appears in every
  resolution of the pencil.
- **Automorphisms have two.**
  - (x − y², y) and (x, y + x²) have [P,Q] = 1.
  - Each pencil, homogenized, has two base points: the origin and [1:0:0], respectively [0:1:0].
  - Over the origin, Φ has residue 1/t after one blow-up.
  - Over the point at infinity, Φ has a non-constant residue after three blow-ups (z₃, respectively −1/w₃).
- **Control.** The identity has one base point and one dicritical.
- **Script.** `reviews/two_dicritical/main_statement_check.py`, with its log (sympy 1.14.0).

So the statement is false as worded. Read literally, it would also make every Keller map injective (two preimages
of one point are two base points of a translated pencil), which is the Jacobian conjecture. The paper's computations
are all at infinity; its definition of a dicritical (line 81, "exceptional divisors on which the pulled-back pencil
has no base points") is not the standard one.

The intended statement, presumably about dicriticals at infinity of a specified pencil, has to be written down
before any proof can be checked against it. Nothing in `lean/` depends on this: `lean/` proves the bridge collapse,
a statement about explicit equations.

### 9.4 The center hypotheses of the bridge are load-bearing

`bridge_collapse` assumes a₃ ≠ 0, a₄ ≠ 0 and a₃ ≠ a₄, as the paper's §3.1 does ("two distinct centers a₃ ≠ a₄ (both
nonzero)"). The paper gives no geometric reason why a bridge center cannot have a = 0. The constant-leading-form
sketch likewise assumes centers with u₀ ≠ 0.

`branch_two_dicritical/lean/TwoDicritical/CenterHypotheses.lean` (standard axioms) shows that each hypothesis is
needed:
- **The witness.** For x − c·y², the weight-2 equation at a center a is a^(d−2)(a − c), and there are no others.
- **A center at 0.** At a₃ = 0 and d ≥ 3, x − a₄y² satisfies every bridge condition. So `bridge_collapse` fails
  without a₃ ≠ 0. With Q = y, the pair (x − a₄y², y) is a polynomial automorphism with Jacobian 1
  (`bridge_jacobian_needs_ne_zero`).
- **Equal centers.** At a₃ = a₄ and d ≥ 2, the same polynomial satisfies every bridge condition.
- **Cross-check.** `lean/check_center_nonzero.py` computes the nullspace from the pullback formula: span{1, y,
  x − a₄y²} at a₃ = 0 for d = 3…6, and span{1, y} at distinct nonzero centers.

PR #18's README listed two modeling premises (the pullback formula, and ã read as an indeterminate). It should
also have listed this one. It does now.

### 9.5 Known limits of #17 and #18, recorded before CAIC's reviews of them arrived

**PR #17** is generic.
- It proves nothing about the concrete chart data, so `ChartEmptyC_T1ne0` stays grade B.
- Its target is `∀ L [Field L] [CharZero L], ChartEmptyC_T1ne0 L`. The definition is stated for any field, but
  every use (`Combine.lean`) carries `[CharZero L]`.

**The 19 `sorry`s of the A1–A5 drafts, against #17.**

| Group | Count | Status after #17 |
|---|---|---|
| A3-1 (`Irreducible R67`, the same polynomial) | 1 | closed |
| SORRY-9 (`rank_of_certificate`) | 1 | stated as `(hC : True) : True`, so empty as written; its intended content is `no_left_kernel` |
| A4-1, A4-2 | 2 | true statements over ℤ that the field argument does not need |
| A4-3 | 1 | assumes an integer root of R: vacuous (§4); its role is taken by `no_common_zero_of_certificate` plus the concrete data |
| A1-1…A1-3 | 3 | untouched |
| A2: SORRY-0 (×2), 1, 2, 2b, 3, 4, 5, 6, 7, 8 | 11 | untouched; they become the hypotheses of `no_common_zero_of_certificate` |

How the untouched A2 items map onto those hypotheses:
- the generators `F`;
- `mon`, `gen` and `mult`, with `hmon`, `hr₁` and `hsupp`;
- `Cinv` with `hC`.

**Data facts** for that work:
- `build_matrix.py` takes the rows to be the supports of the products plus the monomial 1, so `hr₁` and `hsupp`
  hold by construction.
- The generators have rational, 32003-integral coefficients, so they must be scaled into ℤ[X]. The certificate then
  transfers by a diagonal unit rescaling of the columns.

A5's eight axioms are replaced by theorems.

**PR #18** proves the bridge collapse only, not the main theorem.
- Its theorems use the three standard axioms; there are no project axioms.
- `bridgeEq` is checked against the pullback formula for d = 2…6, not for every d.
- Its premises are the three of §9.4.

### 9.6 Open items, updated (replaces §6, items 1 and 5)

1. **Branch (c).** The generic half is in Lean (#17). Remaining:
   - A1, the no-carry argument (3 routine `sorry`s);
   - A2:
     - the six generators with the chart reduction;
     - the rows and pivot columns with `hsupp`;
     - the correspondence of the kernel-checked certificate with `macaulay`, including the rescaling of §9.5.
5. **Two-dicritical.**
   - Correct the statement (§9.3).
   - Justify the three modeling premises of the bridge (§9.4).
   - m ≥ 2 has a sketch only.
   - The adjacent case is done at d = 3 only.
   - The E₁ order translation is not formalized.

   The main theorem is open.
