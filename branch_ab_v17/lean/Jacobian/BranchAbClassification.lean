import Jacobian.BranchAbSharp
import Jacobian.BranchAbTorus

/-!
# Branch (a), (b): the top-layer classification (paper Proposition 6.1, case m = 7)

`TopLayerClassification L` states Proposition 6.1 in exactly the form the descent consumes: every
solution `(A₂, B₃)` of the top-layer equation E5 (`2 A₂ B₃' − 3 A₂' B₃ = λ u²`) with the
Newton-polygon supports and the vertex conditions `a₁,₀, a₈,₁₄, b₂,₁, b₁₂,₂₁ ≠ 0` is a torus image of
one of the five K₅ points `(topA w, topB w)`, where `w` runs over the roots of
`w⁵ − w⁴ + 3w³ + 3w² + 26`.

**Status.** It is stated here, not proved.  The paper proves it through the Belyi map
`φ = u β² / α³` (with `A₂ = u α` and `B₃ = u² β`) and Riemann's existence theorem, together with a
Frobenius character count; Mathlib contains neither.  `BranchAbChart.lean` reduces it
(`topLayerClassification_of_chart`) to `ChartClassification`, a statement about one explicit
17 × 17 polynomial system; see CLASSIFICATION_STATUS.md.

Proved here:
* `orbit_solves_E5`: every torus image of a K₅ point solves E5 with `λ = ρ σ`.  So
  `TopLayerClassification` asserts that there are no other solutions, and the statement is consistent.
* `belyi_derivative` and `layerTerm_top`: the algebraic identities behind the paper's proof,
  `(u β²)' α³ − u β² (α³)' = α² β (α β + 2 u α β' − 3 u α' β)` and
  `2 A₂ B₃' − 3 A₂' B₃ = u² (α β + 2 u α β' − 3 u α' β)`.  Hence E5 is equivalent to `φ' = λ β / α⁴`.
-/

open Polynomial

noncomputable section

namespace BranchAb

/-- **Proposition 6.1 (m = 7), as used by the descent.**  Stated, not proved. -/
def TopLayerClassification (L : Type*) [Field L] : Prop :=
  ∀ (A₂ B₃ : L[X]) (lam : L),
    (∀ i, A₂.coeff i ≠ 0 → 1 ≤ i ∧ i ≤ 8) → (∀ i, B₃.coeff i ≠ 0 → 2 ≤ i ∧ i ≤ 12) →
    A₂.coeff 1 ≠ 0 → A₂.coeff 8 ≠ 0 → B₃.coeff 2 ≠ 0 → B₃.coeff 12 ≠ 0 →
    layerTerm 2 3 A₂ B₃ = C lam * X ^ 2 →
    ∃ w ρ σ ε : L, w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 = 0 ∧ ρ ≠ 0 ∧ σ ≠ 0 ∧ ε ≠ 0 ∧
      (∀ i, A₂.coeff i = ρ * ε ^ (i - 1) * topA w i) ∧ (∀ k, B₃.coeff k = σ * ε ^ (k - 2) * topB w k)

variable {L : Type*} [Field L]

/-- The Belyi-map identity: with `φ = u β² / α³`, `φ' α⁴ = β · (α β + 2 u α β' − 3 u α' β)`. -/
theorem belyi_derivative (α β : L[X]) :
    derivative (X * β ^ 2) * α ^ 3 - X * β ^ 2 * derivative (α ^ 3) =
      α ^ 2 * β * (α * β + 2 * X * α * derivative β - 3 * X * derivative α * β) := by
  simp only [derivative_mul, derivative_X, derivative_pow, one_mul, map_natCast]
  push_cast
  ring

/-- E5 in terms of `α = A₂ / u` and `β = B₃ / u²`. -/
theorem layerTerm_top (α β : L[X]) :
    layerTerm 2 3 (X * α) (X ^ 2 * β) = X ^ 2 * (α * β + 2 * X * α * derivative β - 3 * X * derivative α * β) := by
  simp only [layerTerm, derivative_mul, derivative_X, derivative_X_pow, one_mul, map_natCast]
  push_cast
  ring

lemma sc_C_mul_X_sq (ε c : L) : sc ε (C c * X ^ 2) = C (c * ε ^ 2) * X ^ 2 := by
  simp only [sc, mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow, map_mul]
  ring

/-- **Converse of the classification.**  Every torus image of a K₅ point solves E5, with `λ = ρ σ`. -/
theorem orbit_solves_E5 [CharZero L] (w : L) (hw : w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 = 0)
    (ρ σ ε : L) (hε : ε ≠ 0) (A₂ B₃ : L[X])
    (hA : ∀ i, A₂.coeff i = ρ * ε ^ (i - 1) * topA w i) (hB : ∀ k, B₃.coeff k = σ * ε ^ (k - 2) * topB w k) :
    layerTerm 2 3 A₂ B₃ = C (ρ * σ) * X ^ 2 := by
  obtain ⟨_, _, A, _, _, _, B, hE5, -, -, -, -, -, -, -, -, -, -, cA, cB, -⟩ := layers_K5_sharp w hw
  have eA : A₂ = C (ρ / ε) * sc ε A := by
    ext i
    rw [coeff_C_mul, coeff_sc, cA, hA]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · show ρ * ε ^ (0 - 1) * topA w 0 = ρ / ε * (ε ^ 0 * topA w 0)
      have : topA w 0 = 0 := rfl
      rw [this]; ring
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ]; field_simp
  have eB : B₃ = C (σ / ε ^ 2) * sc ε B := by
    ext k
    rw [coeff_C_mul, coeff_sc, cB, hB]
    rcases Nat.lt_or_ge k 2 with hk | hk
    · have : topB w k = 0 := by interval_cases k <;> rfl
      rw [this]; ring
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      rw [Nat.add_sub_cancel, pow_add]; field_simp
  rw [eA, eB, layerTerm_sc, hE5, sc_C_mul_X_sq, ← mul_assoc, ← C_mul]
  congr 2
  field_simp

end BranchAb
