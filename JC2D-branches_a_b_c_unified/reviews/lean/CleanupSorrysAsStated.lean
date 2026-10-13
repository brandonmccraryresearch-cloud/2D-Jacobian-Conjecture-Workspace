import Mathlib

/-!
# Review witness (2026-10-12, second pass; extended 2026-10-13): seven of the "18 remaining" `sorry`s of the A1–A5
drafts are not proof obligations

After PR #17, CAIC counted "18 remain (A1: 3, A2: 12, A4: 3)" (report relayed on 2026-10-12, 20:43). As the drafts
state them (`caic/branch-c-cleanup`, handoff of 2026-10-12), seven of the 18 close in one line each, and none of the
seven says anything about `ChartEmptyC_T1ne0`:

* A4-1 and A4-2 (`X_eq_zero_of_chart`, `a4_bezout_t1/BezoutT1.lean`): true facts about `Int`, one line together.
  The target is about a field of characteristic 0, where the same step is `mul_eq_zero` and `pow_eq_zero_iff`.
* A4-3 (`chartEmptyC_T1ne0_holds`, same file): its hypothesis `R(w) = 0` with `w : Int` cannot hold (R has no
  integer root), so it closes in one line and proves nothing (see also `A4A5StatementsVacuous.lean`).
* SORRY-9 (`rank_of_certificate`, `a2_macaulay/Macaulay.lean`): its statement is `(hC : True) : True`.
* SORRY-0, twice (`monomialWeight_mul`, `monomialWeight_one`, same file): arithmetic on the draft's own definitions,
  `omega` and `rfl` (added 2026-10-13, after an outside referee's report on PR #19).
* SORRY-4 (`h6_generator_correspondence`, same file): its conclusion is `∃ lam, 0 < lam ∧ True` (added 2026-10-13).

The statements are copied from the drafts; only the proofs are new. A4-3 is generalized over the draft's function
`Xval`, which its proof does not use. Of the other 11, six are `sorry` *definitions*, that is, data still to be
supplied (SORRY-1, 2, 2b, 3, 5, 8). Two are theorems about those definitions (SORRY-6, 7), and SORRY-6 equates the
Lean matrix with `externalMatrix`, which is itself one of the six; neither can be proved until the data exist. Three
are proof obligations (A1's no-carry steps). In the corrected architecture (`branch_c/grade_a/`) the data become the
hypotheses of `no_common_zero_of_certificate`: the generators, the row and column data with the support condition,
and the certificate.
-/

/-- R has no root in ℤ: reduce modulo 67 and check all 67 residues (as in `A4A5StatementsVacuous.lean`). -/
theorem R_no_int_root (w : ℤ) : w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 ≠ 0 := by
  intro hw
  have h : ((w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 : ℤ) : ZMod 67) = 0 := by
    rw [hw]; simp
  push_cast at h
  generalize (w : ZMod 67) = x at h
  revert x h
  decide

/-- A4-1 and A4-2, as stated in `BezoutT1.lean`. -/
theorem X_eq_zero_of_chart (o1 X : Int) (h_omega : o1 * X ^ 2 = 0) (h_bezout : o1 ≠ 0) : X = 0 :=
  (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp h_omega).resolve_left h_bezout)

-- The linter would flag the chart variables as unused: the proof never needs them, which is the point.
set_option linter.unusedVariables false in
/-- A4-3, as stated in `BezoutT1.lean`, for every function `Xval`. -/
theorem chartEmptyC_T1ne0_holds (Xval : Int → Int → Int)
    (w : Int) (hw : w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 = 0)
    (b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21 : Int)
    (ht2 : b_12_22 = 1) (ht1 : b_11_20 ≠ 0) (hX : Xval b_12_23 w = 0) : False :=
  R_no_int_root w hw

-- Again the linter would flag `C` and `hC`: the statement does not use the certificate at all.
set_option linter.unusedVariables false in
/-- SORRY-9, as stated in `Macaulay.lean` (where `K5Coeff := Fin 5 → Rat`). -/
theorem rank_of_certificate (C : Nat → Nat → (Fin 5 → Rat)) (hC : True) : True := trivial

namespace A2Draft

/-- The draft's definitions (`a2_macaulay/Macaulay.lean`, §1 and §2), copied. -/
abbrev Monomial := Fin 5 → Nat

/-- Weighted degree, as in the draft. -/
def monomialWeight (m : Monomial) : Nat :=
  m 0 + 2 * m 1 + 3 * m 2 + 3 * m 3 + 4 * m 4

/-- Monomial multiplication, as in the draft. -/
def monomialMul (m₁ m₂ : Monomial) : Monomial :=
  fun i => m₁ i + m₂ i

/-- The unit monomial, as in the draft. -/
def monomialOne : Monomial := fun _ => 0

/-- The six generator indices, as in the draft. -/
inductive GenIdx where
  | Psi | Phi1 | Phi2 | Theta1 | Theta2 | Theta3
  deriving DecidableEq, Repr

/-- SORRY-0 (first), as stated. -/
theorem monomialWeight_mul (m₁ m₂ : Monomial) :
    monomialWeight (monomialMul m₁ m₂) = monomialWeight m₁ + monomialWeight m₂ := by
  simp only [monomialWeight, monomialMul]; omega

/-- SORRY-0 (second), as stated. -/
theorem monomialWeight_one : monomialWeight monomialOne = 0 := rfl

-- The linter would flag `n`: the conclusion never mentions it, which is the point.
set_option linter.unusedVariables false in
/-- SORRY-4, as stated: the conclusion does not mention the generators. -/
theorem h6_generator_correspondence :
    ∀ n : GenIdx, ∃ lam : Nat, 0 < lam ∧
      -- `chartGenerators n` equals `lam` times the CondsC condition after substitution
      True :=
  fun _ => ⟨1, Nat.one_pos, trivial⟩

end A2Draft

#print axioms X_eq_zero_of_chart
#print axioms chartEmptyC_T1ne0_holds
#print axioms rank_of_certificate
#print axioms A2Draft.monomialWeight_mul
#print axioms A2Draft.monomialWeight_one
#print axioms A2Draft.h6_generator_correspondence
