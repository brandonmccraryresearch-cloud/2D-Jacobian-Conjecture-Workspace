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
| `a4_bezout_t1/BezoutT1.lean` | 3 | 0 | Stated over `Int`. **A4-3 is vacuous**: it assumes a root of R in `Int`, where R has none. (Corrected in §9.5: A4-1 and A4-2 are true facts about `Int`, not vacuous, but the field argument does not need them.) |
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
# the review witnesses (any Lean 4.34 + Mathlib v4.34 project); the third was added in §9.7
lake env lean ../../reviews/lean/A4A5StatementsVacuous.lean
lake env lean ../../reviews/lean/BridgeAxiomsInconsistent.lean
lake env lean ../../reviews/lean/CleanupSorrysAsStated.lean
# two-dicritical (§9.3–9.4, corrected 2026-10-13): the statement, then the Lean build (~2 min) and its checks
python3 ../../reviews/two_dicritical/main_statement_check.py
python3 ../../reviews/two_dicritical/base_point_at_infinity_check.py
bash ../../../branch_two_dicritical/lean/build.sh "$PWD"
(cd ../../../branch_two_dicritical/lean && python3 check_satellite.py && python3 check_e1_index.py)
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
  #17 and #18 together with §9.3–9.4 below. At `d6e4c4f`, `grade_a/` was byte-identical to `4af460e` and
  `branch_two_dicritical/lean/` to `696e59d`. Later commits on the branch changed `grade_a/README.md`, `build.sh` and
  `logs/build.log` (`0a6c001`), and changed and added to `branch_two_dicritical/lean/`; the Lean sources of #17, and
  `BlockRank.lean`, `E1Obstruction.lean` and `BridgeCollapse.lean` of #18, are unchanged.

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

So the statement is false as worded, and not only for these two maps (strengthened on 2026-10-13, after an outside
referee's report on PR #19):
- **Every Keller map of degree ≥ 2 has a base point at infinity.**
  - With equal degrees d ≥ 2, the Jacobian of the top forms is the degree-(2d − 2) part of [P,Q], so it vanishes,
    and two binary forms of the same degree with vanishing Jacobian are proportional.
  - With unequal degrees, Qʰ vanishes on the whole line at infinity.
  - `reviews/two_dicritical/base_point_at_infinity_check.py` has the argument in its header and checks it on 30
    random automorphisms, with affine maps as the control.
- **An affine base point.** After a translation of the target that makes 0 a value (none is needed for an
  automorphism), there is also an affine base point.
- **Consequence.** Every Keller map of degree ≥ 2 refutes the statement as worded. Read literally, the statement
  would also imply the Jacobian conjecture outright (two preimages of one point are two base points of a translated
  pencil). That alone would not make it false; the base point at infinity does.
- **The referee's sketch, not checked here.** An automorphism of degree ≥ 2 has exactly two dicriticals, one over
  F⁻¹(0) and one at infinity (pull back the pencil of lines through the origin). If true, any corrected statement
  must pass this test first.

The paper's computations are all at infinity; its definition of a dicritical (line 81, "exceptional divisors on which
the pulled-back pencil has no base points") is not the standard one.

The intended statement, presumably about dicriticals at infinity of a specified pencil, has to be written down
before any proof can be checked against it. Nothing in `lean/` depends on this: `lean/` proves the bridge collapse,
a statement about explicit equations.

### 9.4 The bridge's center hypotheses, and Theorem `thm:e1` (corrected 2026-10-13)

*Corrected on 2026-10-13, after an outside referee's report on PR #19. Each point below was re-derived and executed
before it was accepted (`branch_two_dicritical/lean/check_satellite.py`, `check_e1_index.py`, with their logs).*

`bridge_collapse` assumes a₃ ≠ 0, a₄ ≠ 0 and a₃ ≠ a₄, as the paper's §3.1 does ("two distinct centers a₃ ≠ a₄ (both
nonzero)"). `branch_two_dicritical/lean/TwoDicritical/CenterHypotheses.lean` (standard axioms) shows that none of them
can be dropped from the theorem about the equations:
- **The witness.** For x − c·y², the weight-2 equation at a center a is a^(d−2)(a − c), and there are no others.
- **A center at 0.** At a₃ = 0 and d ≥ 3, x − a₄y² satisfies every equation. With Q = y the pair (x − a₄y², y) has
  Jacobian 1 (`bridge_jacobian_needs_ne_zero`).
- **Equal centers.** At a₃ = a₄ and d ≥ 2, the same polynomial satisfies every equation.
- **Cross-check.** `lean/check_center_nonzero.py` computes the nullspace from the pullback formula: span{1, y,
  x − a₄y²} at a₃ = 0 for d = 3…6, and span{1, y} at distinct nonzero centers.

The first version of this section concluded that "both centers nonzero" is load-bearing and unjustified, and that the
paper must show a bridge center cannot sit at a = 0. **That reading was wrong.**
- **The formula is a chart.** The pullback formula is Sʰ(1, b, b²(a + ãb)): the chart at the point w₂ = a of E₂, the
  second exceptional curve over [1:0:0], with w₂ = x/y². For a ≠ 0 the point is free, and ord_b S_a ≥ 2d − 1 says
  ν ≥ −1 on the divisor over a.
- **a = 0 is a satellite point**, where E₂ meets the line at infinity. There the factor Zᵈ is ãᵈb^(3d), so the same
  threshold says ν ≥ −(d + 1), and raising d weakens it. The witness has degree 2 and works only for d ≥ 3.
- **The witness is not a bridge.** Over a = 0 its P/Q has a pole. Its only dicritical at infinity lies over the free
  point a₄, where P/Q restricts to ã/a₄: a one-center configuration.
- **The right condition at 0 empties the system.** Read as ν ≥ −1 (ord_b S₀ ≥ 3d − 1), the conditions at the centers
  0 and 5 leave only constants (d = 2…6). With d read as the exact degree, the hypothesis is not needed for d ≥ 3
  (`OneCenter.lean`, `zero_center_no_top_degree`).

Read through this chart, the bridge rests on two premises:
- (P1) the two dicriticals are the divisors over two distinct free points of this E₂;
- (P2) every member of the pencil has ν ≥ −1 on them.

Reading ã as an indeterminate is not a further premise: it is how ν is computed.
- **(P2) is asserted, not derived.** The paper defines m as the degree of the pencil's restriction, and degree 1 does
  not force pole order 1 (`check_satellite.py`, check 7).
- **Scope.** Under (P1) and (P2), one dicritical already forces degree ≤ 2 (`bridge_one_center`), so the bridge says
  nothing about pencils of degree ≥ 3.
- **What is not treated.** Dicriticals over the satellite points of E₂ and deeper are treated neither by the bridge
  nor by the constant-leading-form sketch (which assumes centers with u₀ ≠ 0). The automorphism (x + y³, y) has its
  dicritical at infinity over a = ∞.

**Theorem `thm:e1` is false as stated.** This review had not checked it.
- **The index mix-up.** ν_{E₁}(x^i y^j) = −i, so ν_{E₁} ≥ −2 means x-degree ≤ 2. `e1_solitary.py` indexes its unknowns
  by X^(d−J−K)Y^J Z^K. The paper's proof, `e1_keller_search.py` and `E1Obstruction.lean` read them as x^J y^K, which
  gives "total degree ≥ 2". At d = 4 both sets have 12 monomials.
- **The counterexample.** P = (x + y²)² + y and Q = P + x + y² satisfy the paper's definition of the E₁ m = 2 open
  subset and have [P,Q] = −1 (`thm_e1_false` in `E1Keller.lean`).
- **The intended conclusion is true for every m: E₁ is never dicritical for a Keller map.**
  - The x^(2n−1)-coefficient of [P,Q] is n(AD′ − A′D) for the leading x-coefficients A, D, and a vanishing
    Wronskian forces A ∝ D (`e1_lead_proportional`).
  - The chart step, that P/Q restricts to A/D on E₁, is executed, not formalized.

PR #18's README listed two modeling premises (the pullback formula, and ã read as an indeterminate), and the first
version of this section added "both centers nonzero". The list is now (P1) and (P2).

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

Witness for the second, third and fourth rows: `reviews/lean/CleanupSorrysAsStated.lean` (added in §9.7) closes
SORRY-9 and A4-1…A4-3 as stated, in one line each. Since 2026-10-13 it also closes SORRY-0 (×2) and SORRY-4, which
the last row lists as untouched (§9.7).

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
- Its premises are (P1) and (P2) of §9.4 (as corrected on 2026-10-13).

### 9.6 Open items, updated (replaces §6, items 1 and 5)

1. **Branch (c).** The generic half is in Lean (#17). Remaining:
   - A1, the no-carry argument (3 routine `sorry`s);
   - A2:
     - the six generators with the chart reduction;
     - the rows and pivot columns with `hsupp`;
     - the correspondence of the kernel-checked certificate with `macaulay`, including the rescaling of §9.5.
5. **Two-dicritical** (corrected 2026-10-13).
   - Correct the statement (§9.3).
   - The bridge: derive (P2) from the definition of m, or state it as a hypothesis; treat dicriticals over the
     satellite points of E₂ and deeper (§9.4).
   - m ≥ 2 on E_k, k ≥ 2, has a sketch only, and for free centers only.
   - The adjacent case is done at d = 3 only.
   - E₁: Theorem `thm:e1` is false as stated. The corrected statement, that E₁ is never dicritical for a Keller map,
     has its algebraic step in Lean; its chart step is executed only (§9.4).

   The main theorem is open.

### 9.7 CAIC's verdicts on #17 and #18, against §9.5

Brandon relayed CAIC's reports on #17 and #18 at 20:43. Their text predates §9.3–9.4 and PR #19: they recommend
merging #16–#18 "in stack order", although all three were merged at 16:08–16:10. CAIC counts 18 claims across
#16–#18, all confirmed. Against the expectations of §9.5:

| §9.5 expectation | CAIC's verdict | Agreement |
|---|---|---|
| #17 is generic; `ChartEmptyC_T1ne0` stays grade B | the same | yes |
| #17 closes one `sorry` (A3-1) | "exactly one sorry closed (A3's)" | yes |
| of the other 18: SORRY-9 empty as stated, A4 retired, 14 untouched | "18 remain (A1: 3, A2: 12, A4: 3)" | **half** (corrected 2026-10-13): both counts are of `sorry` tokens, this review's "14 untouched" included. By kind: seven close in one line each as stated (A4-1…A4-3, SORRY-9, SORRY-0 ×2, SORRY-4; `reviews/lean/CleanupSorrysAsStated.lean`), and none of them says anything about the target; six are definitions still to be supplied (SORRY-1, 2, 2b, 3, 5, 8); two are theorems about those definitions (SORRY-6, 7); three are proof obligations (A1) |
| #18 uses the standard axioms and does not import `Bridge.lean` | the same, from CAIC's own `#print axioms` | yes |
| `bridgeEq` is checked for d = 2…6 only | "independent computation … not circular" | the finite range is not mentioned |
| the bridge has three modeling premises | "five open items, nothing material omitted" | **half** (corrected 2026-10-13): on the centers CAIC was right, since "both centers nonzero" marks where the formula applies (§9.4). CAIC's verdict missed that the statement is false as worded (§9.3), and both reviews missed that Theorem `thm:e1` is false as stated (§9.4) |
| #18 proves the bridge lemma, not the main theorem | the same | yes |

Further points in CAIC's reports, checked:
- **Build time.** #17's description said the build took 106 s, while the committed log (the from-scratch rebuild at
  `4af460e`) sums to 117 s, and 119 s with the scan and the axiom step. CAIC is right; the description is corrected.
- **W = 2 is the only failing weight.** For W ≥ 3 a block has at most ⌊W/2⌋ + 1 ≤ W − 1 unknowns. This is what the
  `omega` step of `bridge_collapse` checks. CAIC places the bridge in the paper's §4; it is §3, with the gap in §3.2.
- **BlockRank warnings.** `BlockRank.lean` emits four cosmetic warnings: one deprecated `push_neg` and three unused
  section variables. CAIC reports a cleaned version, which is not yet in the repository.
