-- PLANTED CONTROL (must FAIL to compile): the paper's lem:binary without g ≠ 0.
import O5.O5
open MvPolynomial
theorem control_binary_without_g_ne_zero :
    ∀ (f g : MvPolynomial (Fin 2) ℚ) (d : ℕ), 1 ≤ d → f.IsHomogeneous d → g.IsHomogeneous d →
      O5.jacobian f g = 0 → ∃ r : ℚ, f = C r * g := by
  intro f g d hd hf hg hj
  exact O5.binary_form_proportional hd hf hg (by sorry) hj
#print axioms control_binary_without_g_ne_zero
