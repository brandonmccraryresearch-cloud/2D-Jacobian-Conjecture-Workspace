import Mathlib

/-!
# `R` modulo 67: the two finite checks

`R = X⁵ − X⁴ + 3X³ + 3X² + 26`. Both statements are decided by the Lean kernel on integers (`decide`), with no
`native_decide`:
* `R_no_root_int`: `67 ∤ R(n)` for `n = 0, …, 66`;
* `rem_not_both_zero`: for each of the 67² monic quadratics `X² + aX + b` over `𝔽₆₇`, the remainder of `R` modulo it,
  `remX(a,b)·X + remC(a,b)`, is not zero modulo 67.

The formulas for the remainder are checked against the division identity in `IrreducibleR.lean` (`R67_div`).
They follow the draft `a3_irreducibility_transfer/IrreducibleR.lean` of the branch `caic/branch-c-cleanup`.
-/

namespace BranchC.GradeA

/-- `67 ∤ R(n)` for `n = 0, …, 66`. -/
theorem R_no_root_int : ∀ a : Fin 67,
    ¬ (67 : ℤ) ∣ ((a.val : ℤ) ^ 5 - (a.val : ℤ) ^ 4 + 3 * (a.val : ℤ) ^ 3 + 3 * (a.val : ℤ) ^ 2 + 26) := by
  decide

/-- Coefficient of `X` in the remainder of `R` divided by `X² + aX + b`. -/
def remX (a b : ℤ) : ℤ := a ^ 4 - 3 * a ^ 2 * b + b ^ 2 + a ^ 3 - 2 * a * b + 3 * a ^ 2 - 3 * b - 3 * a

/-- Constant term of the remainder of `R` divided by `X² + aX + b`. -/
def remC (a b : ℤ) : ℤ := a ^ 3 * b - 2 * a * b ^ 2 + a ^ 2 * b - b ^ 2 + 3 * a * b - 3 * b + 26

/-- The remainder is never zero modulo 67 (all 4489 pairs). -/
theorem rem_not_both_zero : ∀ a b : Fin 67,
    ¬ ((67 : ℤ) ∣ remX (a.val : ℤ) (b.val : ℤ) ∧ (67 : ℤ) ∣ remC (a.val : ℤ) (b.val : ℤ)) := by
  decide

end BranchC.GradeA
