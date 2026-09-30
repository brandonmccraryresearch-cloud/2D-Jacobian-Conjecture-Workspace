import Jacobian.BranchC.Edge19
import Jacobian.BranchC.OmegaEdge
import Jacobian.BranchC.LayersGen

/-! Negative controls for the new branch-(c) lemmas: each shows that a hypothesis is load-bearing or that
a mutated conclusion is false. Not part of the library. -/

open BranchC

/-- Control 1: without `α ≠ 0` the rigidity fails: `α = a₁ = a₀ = 0`, `β = 1`, `t = 0`, `s = 1`, `b = 0`
satisfy all four edge equations but `3βs ≠ t²`. -/
theorem ctrl_edge_needs_alpha :
    ∃ α a₁ a₀ β t s b : ℚ, 2 * α * t - 3 * β * a₁ = 0 ∧ 4 * α * s - a₁ * t - 6 * β * a₀ = 0 ∧
      6 * α * b + a₁ * s - 4 * a₀ * t = 0 ∧ 3 * a₁ * b - 2 * a₀ * s = 0 ∧ 3 * β * s ≠ t ^ 2 :=
  ⟨0, 0, 0, 1, 0, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Control 2: the `y³⁸` equation is load-bearing for `3βs = t²`: with only the first three equations,
`α = β = 1`, `t = 0`, `s = 3`, `a₁ = 0`, `a₀ = 2`, `b = 0` is a solution with `3βs = 9 ≠ 0 = t²`. -/
theorem ctrl_edge_needs_y38 :
    ∃ α a₁ a₀ β t s b : ℚ, α ≠ 0 ∧ 2 * α * t - 3 * β * a₁ = 0 ∧ 4 * α * s - a₁ * t - 6 * β * a₀ = 0 ∧
      6 * α * b + a₁ * s - 4 * a₀ * t = 0 ∧ 3 * β * s ≠ t ^ 2 :=
  ⟨1, 0, 2, 1, 0, 3, 0, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Control 3: `κ = 38` is the right root mod 101 and the neighbouring value is not: `Ω(1, 38) = 0` but
`Ω(1, 39) ≠ 0` in `𝔽₁₀₁` (`c = (69, 8, 50)`). -/
theorem ctrl_kappa_mod101 : (69 * 38 ^ 2 + 8 * 38 + 50 : ZMod 101) = 0 ∧ (69 * 39 ^ 2 + 8 * 39 + 50 : ZMod 101) ≠ 0 := by
  decide

/-- Control 4: the layer operator sign convention. For `A = u`, `B = λu²` (the pair `P = x`, `Q = λx²y`),
`LT_{2,3}(A,B) = λu²`, while the swapped convention `3AB′ − 2A′B` gives `4λu²`. -/
theorem ctrl_layer_sign (lam : ℚ) (h : lam ≠ 0) :
    layerTermZ 2 3 (Polynomial.X) (Polynomial.C lam * Polynomial.X ^ 2) = Polynomial.C lam * Polynomial.X ^ 2 ∧
    layerTermZ 3 2 (Polynomial.X) (Polynomial.C lam * Polynomial.X ^ 2) ≠ Polynomial.C lam * Polynomial.X ^ 2 := by
  have e : ∀ a b : ℤ, layerTermZ a b (Polynomial.X) (Polynomial.C lam * Polynomial.X ^ 2) =
      Polynomial.C ((2 * a - b) * lam) * Polynomial.X ^ 2 := by
    intro a b
    simp only [layerTermZ, Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
      Polynomial.derivative_X_pow, zero_mul, zero_add, map_mul, map_sub, map_ofNat, map_intCast, Nat.cast_ofNat]
    ring
  constructor
  · rw [e]; norm_num
  · intro hc
    rw [e] at hc
    have h2 := congrArg (fun p => Polynomial.coeff p 2) hc
    simp only [Polynomial.coeff_C_mul_X_pow, ite_true] at h2
    norm_num at h2
    exact h (by linarith)
