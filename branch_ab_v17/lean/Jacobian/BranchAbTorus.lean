import Jacobian.BranchAbLayers

/-!
# Branch (a), (b): torus transport of the layer identities (Lemma 9.1(v))

Rescaling `u ↦ κ u` together with constant multiples `α`, `β` of the P- and Q-layers multiplies every
layer term `a A B' − b A' B` by the same constant `α β κ` (and composes with `u ↦ κ u`).  Hence the
layer identities E4, E3, E2 and the supports are preserved, and the top layer moves along its torus
orbit.  This is the formal content of the transport step in Lemma 9.1(v): an obstruction proved at
one top layer holds at every top layer in its orbit.
-/

open Polynomial

noncomputable section

namespace BranchAb

variable {K : Type*} [Field K]

/-- `F(u) ↦ F(κ u)`. -/
def sc (κ : K) (F : K[X]) : K[X] := F.comp (C κ * X)

lemma coeff_sc (κ : K) (F : K[X]) (i : ℕ) : (sc κ F).coeff i = κ ^ i * F.coeff i := by
  unfold sc
  induction F using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow, ← mul_assoc,
      ← C_mul, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; ring
    · simp

lemma derivative_sc (κ : K) (F : K[X]) :
    derivative (sc κ F) = C κ * sc κ (derivative F) := by
  unfold sc
  rw [derivative_comp, derivative_C_mul_X]

lemma layerTerm_sc (α β κ : K) (a b : ℕ) (A B : K[X]) :
    layerTerm a b (C α * sc κ A) (C β * sc κ B) = C (α * β * κ) * sc κ (layerTerm a b A B) := by
  simp only [layerTerm, derivative_mul, derivative_C, zero_mul, zero_add, derivative_sc]
  simp only [sc, sub_comp, mul_comp, natCast_comp, C_mul]
  ring

/-- Transport of E4, E3, E2 along the torus. -/
theorem layers_transport (α β κ : K) (A₀ A₁ A₂ B₀ B₁ B₂ B₃ : K[X])
    (E4 : layerTerm 2 2 A₂ B₂ + layerTerm 1 3 A₁ B₃ = 0)
    (E3 : layerTerm 2 1 A₂ B₁ + layerTerm 1 2 A₁ B₂ + layerTerm 0 3 A₀ B₃ = 0)
    (E2 : layerTerm 2 0 A₂ B₀ + layerTerm 1 1 A₁ B₁ + layerTerm 0 2 A₀ B₂ = 0) :
    layerTerm 2 2 (C α * sc κ A₂) (C β * sc κ B₂) + layerTerm 1 3 (C α * sc κ A₁) (C β * sc κ B₃) = 0 ∧
    layerTerm 2 1 (C α * sc κ A₂) (C β * sc κ B₁) + layerTerm 1 2 (C α * sc κ A₁) (C β * sc κ B₂) +
      layerTerm 0 3 (C α * sc κ A₀) (C β * sc κ B₃) = 0 ∧
    layerTerm 2 0 (C α * sc κ A₂) (C β * sc κ B₀) + layerTerm 1 1 (C α * sc κ A₁) (C β * sc κ B₁) +
      layerTerm 0 2 (C α * sc κ A₀) (C β * sc κ B₂) = 0 := by
  simp only [layerTerm_sc, ← mul_add]
  simp only [sc, ← add_comp, E4, E3, E2, zero_comp, mul_zero, and_self]

end BranchAb
