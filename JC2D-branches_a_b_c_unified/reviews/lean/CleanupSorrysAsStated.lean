import Mathlib

/-!
# Review witness (2026-10-12, second pass): four of the "18 remaining" `sorry`s of the A1–A5 drafts are not proof
obligations

After PR #17, CAIC counted "18 remain (A1: 3, A2: 12, A4: 3)" (report relayed on 2026-10-12, 20:43). As the drafts
state them (`caic/branch-c-cleanup`, handoff of 2026-10-12), four of the 18 close in one line each, and none of the
four says anything about `ChartEmptyC_T1ne0`:

* A4-1 and A4-2 (`X_eq_zero_of_chart`, `a4_bezout_t1/BezoutT1.lean`): true facts about `Int`, one line together.
  The target is about a field of characteristic 0, where the same step is `mul_eq_zero` and `pow_eq_zero_iff`.
* A4-3 (`chartEmptyC_T1ne0_holds`, same file): its hypothesis `R(w) = 0` with `w : Int` cannot hold (R has no
  integer root), so it closes in one line and proves nothing (see also `A4A5StatementsVacuous.lean`).
* SORRY-9 (`rank_of_certificate`, `a2_macaulay/Macaulay.lean`): its statement is `(hC : True) : True`.

The statements are copied from the drafts; only the proofs are new. A4-3 is generalized over the draft's function
`Xval`, which its proof does not use. The other 14 (A1: 3; A2: SORRY-0 (×2), 1, 2, 2b, 3, 4, 5, 6, 7, 8) are where
the remaining work is. In the corrected architecture they become the hypotheses of
`no_common_zero_of_certificate` (`branch_c/grade_a/`): the generators, the row and column data with the support
condition, and the certificate.
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

#print axioms X_eq_zero_of_chart
#print axioms chartEmptyC_T1ne0_holds
#print axioms rank_of_certificate
