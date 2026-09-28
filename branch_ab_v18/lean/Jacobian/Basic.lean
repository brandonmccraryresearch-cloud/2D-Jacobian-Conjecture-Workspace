import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

open MvPolynomial

/-- The ambient fraction field: rational functions in two variables over a field k. -/
abbrev AmbientFractionField (k : Type*) [Field k] : Type _ :=
  FractionRing (MvPolynomial (Fin 2) k)

/-- Valuative properness for a polynomial map (P, Q) : 𝔸² → 𝔸².

A map is valuatively proper if every place at infinity (every additive
valuation v with v(X) < 0 or v(Y) < 0, i.e. a pole along some direction
at infinity) gives a pole of P or a pole of Q. Equivalently: no branch
at infinity is dicritical (finite non-zero limit) for both P and Q.

Uses AddValuation with value group WithTop ℤ (additive convention:
v(x) < 0 means pole, v(x) > 0 means zero, v(x) = 0 means unit).
-/
def IsValuativelyProper2D {k : Type*} [Field k]
    (P Q : MvPolynomial (Fin 2) k) : Prop :=
  ∀ (v : AddValuation (AmbientFractionField k) (WithTop ℤ)),
    (∀ α : k, α ≠ 0 → v (algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (C α)) = 0) →
    (v (algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (X 0)) < 0 ∨
     v (algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (X 1)) < 0) →
    (v (algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) P) < 0 ∨
     v (algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) Q) < 0)

/-- Scalars have non-negative valuation under a place trivial on k×.

If α = 0, then v(0) = ⊤ ≥ 0. If α ≠ 0, then v(C α) = 0 by triviality.
-/
lemma val_C_ge_zero {k : Type*} [Field k]
    (v : AddValuation (AmbientFractionField k) (WithTop ℤ))
    (h_triv : ∀ α : k, α ≠ 0 → v (algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (C α)) = 0)
    (α : k) :
    0 ≤ v (algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (C α)) := by
  by_cases hα : α = 0
  · subst hα
    rw [C_0, map_zero, v.map_zero]
    exact le_top
  · rw [h_triv α hα]

/-- Scaling by a scalar preserves non-negativity of valuation.

v(c * x) = v(c) + v(x) ≥ 0 + 0 = 0 when v(c) ≥ 0 and v(x) ≥ 0.
-/
lemma val_mul_scalar_ge_zero {k : Type*} [Field k]
    (v : AddValuation (AmbientFractionField k) (WithTop ℤ))
    (h_triv : ∀ α : k, α ≠ 0 → v (algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (C α)) = 0)
    (α : k) (x : AmbientFractionField k) (hx : 0 ≤ v x) :
    0 ≤ v (algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (C α) * x) := by
  rw [v.map_mul]
  have hC := val_C_ge_zero v h_triv α
  -- In WithTop ℤ, sum of non-negatives is non-negative
  calc (0 : WithTop ℤ) ≤ 0 + 0 := le_refl _
    _ ≤ v (algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (C α)) + v x :=
        add_le_add hC hx

/-- The identity coordinate map is valuatively proper. -/
theorem isValuativelyProper2D_id {k : Type*} [Field k] :
    IsValuativelyProper2D (X 0 : MvPolynomial (Fin 2) k) (X 1) := by
  intro v h_triv h_hyp
  exact h_hyp

/-- Triangular automorphisms satisfy valuative properness.

This is the base case of the Jung–van der Kulk induction: the map
(X, Y) ↦ (X + Y², Y) is proper, and the valuative predicate detects this.
-/
theorem isValuativelyProper2D_triangular {k : Type*} [Field k] :
    IsValuativelyProper2D ((X 0 : MvPolynomial (Fin 2) k) + (X 1)^2) (X 1) := by
  intro v h_triv h_hyp
  -- h_hyp : v (ι (X 0)) < 0 ∨ v (ι (X 1)) < 0
  -- Goal: v (ι (X 0 + X 1^2)) < 0 ∨ v (ι (X 1)) < 0
  -- Note: h_triv is unused; the triangular case needs no scalar valuations.
  -- Case split on whether X 1 is already at infinity
  by_cases h1 : v (algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (X 1)) < 0
  · -- Case 1: v(X₁) < 0, so Q = X₁ already has a pole
    exact Or.inr h1
  · -- Case 2: v(X₁) ≥ 0, so v(X₀) < 0 must hold
    have h1_ge : 0 ≤ v (algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (X 1)) :=
      not_lt.mp h1
    have h0 : v (algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (X 0)) < 0 := by
      cases h_hyp with
      | inl h0' => exact h0'
      | inr h1' => exact False.elim (h1 h1')
    -- Show the left disjunct: v(P) < 0 where P = X₀ + X₁²
    apply Or.inl
    -- Push algebraMap through addition and power
    have h_map : algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k)
        ((X 0 : MvPolynomial (Fin 2) k) + (X 1)^2)
        = algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (X 0)
          + (algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (X 1))^2 := by
      rw [map_add, map_pow]
    rw [h_map]
    -- v(X₁²) = 2 • v(X₁) ≥ 0
    have h1_sq : v ((algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (X 1))^2)
        = 2 • v (algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (X 1)) :=
      v.map_pow _ 2
    have h1_sq_ge : 0 ≤ v ((algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (X 1))^2) := by
      rw [h1_sq]
      -- 2 • a ≥ 0 when a ≥ 0 in WithTop ℤ
      have : (0 : WithTop ℤ) ≤ 2 • v (algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (X 1)) := by
        apply nsmul_nonneg h1_ge 2
      exact this
    -- v(X₀) < 0 ≤ v(X₁²), so v(X₀) < v(X₁²)
    have h_lt : v (algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (X 0))
        < v ((algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k) (X 1))^2) :=
      lt_of_lt_of_le h0 h1_sq_ge
    -- Strict ultrametric: v(a+b) = v(a) when v(a) < v(b)
    have h_sum := v.map_add_eq_of_lt_left h_lt
    rw [h_sum]
    exact h0

/-- Linear coordinate changes with non-zero determinant preserve valuative properness.

Given (P, Q) valuatively proper and a matrix [[a,b],[c,d]] with Δ = ad-bc ≠ 0,
the transformed pair (aP+bQ, cP+dQ) is valuatively proper.

Proof strategy: by contradiction. If v(P') ≥ 0 and v(Q') ≥ 0, reconstruct
P = (d/Δ)P' - (b/Δ)Q' and Q = (-c/Δ)P' + (a/Δ)Q'. Since scalars have
non-negative valuation (Lemma A) and scaling preserves this (Lemma B),
each summand has v ≥ 0, so v(P) ≥ 0 and v(Q) ≥ 0 by the ultrametric
inequality, contradicting valuative properness of (P, Q).
-/
theorem isValuativelyProper2D_linear {k : Type*} [Field k]
    (P Q : MvPolynomial (Fin 2) k)
    (h_prop : IsValuativelyProper2D P Q)
    (a b c d : k) (h_det : a * d - b * c ≠ 0) :
    IsValuativelyProper2D (C a * P + C b * Q) (C c * P + C d * Q) := by
  intro v h_triv h_hyp
  have h_orig := h_prop v h_triv h_hyp
  by_contra h_neg
  push Not at h_neg
  rcases h_neg with ⟨hP', hQ'⟩
  -- After push_neg: hP' : 0 ≤ v(ι(P')), hQ' : 0 ≤ v(ι(Q'))
  let ι := algebraMap (MvPolynomial (Fin 2) k) (AmbientFractionField k)
  let Δ := a * d - b * c
  -- Reconstructed coordinates in the fraction field
  -- P = (d/Δ)·P' + (-b/Δ)·Q', Q = (-c/Δ)·P' + (a/Δ)·Q'
  -- 1. Discharge hP_recon via polynomial-level identity
  have hP_poly : (C (d / Δ) : MvPolynomial (Fin 2) k) * (C a * P + C b * Q)
      + C (-b / Δ) * (C c * P + C d * Q) = P := by
    have h1 : (C (d / Δ) : MvPolynomial (Fin 2) k) * C a + C (-b / Δ) * C c = 1 := by
      rw [← C_mul, ← C_mul, ← C_add]
      have : d / Δ * a + -b / Δ * c = (a * d - b * c) / Δ := by ring
      rw [this, div_self h_det, map_one]
    have h2 : (C (d / Δ) : MvPolynomial (Fin 2) k) * C b + C (-b / Δ) * C d = 0 := by
      rw [← C_mul, ← C_mul, ← C_add]
      have : d / Δ * b + -b / Δ * d = 0 := by ring
      rw [this, map_zero]
    calc (C (d / Δ) : MvPolynomial (Fin 2) k) * (C a * P + C b * Q) + C (-b / Δ) * (C c * P + C d * Q)
      _ = (C (d / Δ) * C a + C (-b / Δ) * C c) * P + (C (d / Δ) * C b + C (-b / Δ) * C d) * Q := by ring
      _ = 1 * P + 0 * Q := by rw [h1, h2]
      _ = P := by ring
  have hP_recon : ι P = ι (C (d / Δ)) * ι (C a * P + C b * Q)
      + ι (C (-b / Δ)) * ι (C c * P + C d * Q) := by
    rw [← map_mul, ← map_mul, ← map_add, hP_poly]
  -- 2. Discharge hQ_recon via polynomial-level identity
  have hQ_poly : (C (-c / Δ) : MvPolynomial (Fin 2) k) * (C a * P + C b * Q)
      + C (a / Δ) * (C c * P + C d * Q) = Q := by
    have h1 : (C (-c / Δ) : MvPolynomial (Fin 2) k) * C a + C (a / Δ) * C c = 0 := by
      rw [← C_mul, ← C_mul, ← C_add]
      have : -c / Δ * a + a / Δ * c = 0 := by ring
      rw [this, map_zero]
    have h2 : (C (-c / Δ) : MvPolynomial (Fin 2) k) * C b + C (a / Δ) * C d = 1 := by
      rw [← C_mul, ← C_mul, ← C_add]
      have : -c / Δ * b + a / Δ * d = (a * d - b * c) / Δ := by ring
      rw [this, div_self h_det, map_one]
    calc (C (-c / Δ) : MvPolynomial (Fin 2) k) * (C a * P + C b * Q) + C (a / Δ) * (C c * P + C d * Q)
      _ = (C (-c / Δ) * C a + C (a / Δ) * C c) * P + (C (-c / Δ) * C b + C (a / Δ) * C d) * Q := by ring
      _ = 0 * P + 1 * Q := by rw [h1, h2]
      _ = Q := by ring
  have hQ_recon : ι Q = ι (C (-c / Δ)) * ι (C a * P + C b * Q)
      + ι (C (a / Δ)) * ι (C c * P + C d * Q) := by
    rw [← map_mul, ← map_mul, ← map_add, hQ_poly]
  -- Each summand has non-negative valuation by Lemma B
  have hP1 : 0 ≤ v (ι (C (d / Δ)) * ι (C a * P + C b * Q)) :=
    val_mul_scalar_ge_zero v h_triv (d / Δ) _ hP'
  have hP2 : 0 ≤ v (ι (C (-b / Δ)) * ι (C c * P + C d * Q)) :=
    val_mul_scalar_ge_zero v h_triv (-b / Δ) _ hQ'
  -- v(P) ≥ min(v(summand₁), v(summand₂)) ≥ 0
  have hP_ge : 0 ≤ v (ι P) := by
    rw [hP_recon]
    exact le_trans (le_min hP1 hP2) (v.map_add _ _)
  have hQ1 : 0 ≤ v (ι (C (-c / Δ)) * ι (C a * P + C b * Q)) :=
    val_mul_scalar_ge_zero v h_triv (-c / Δ) _ hP'
  have hQ2 : 0 ≤ v (ι (C (a / Δ)) * ι (C c * P + C d * Q)) :=
    val_mul_scalar_ge_zero v h_triv (a / Δ) _ hQ'
  have hQ_ge : 0 ≤ v (ι Q) := by
    rw [hQ_recon]
    exact le_trans (le_min hQ1 hQ2) (v.map_add _ _)
  -- Contradiction with h_orig : v(ι P) < 0 ∨ v(ι Q) < 0
  cases h_orig with
  | inl hP_lt => exact absurd hP_lt (not_lt.mpr hP_ge)
  | inr hQ_lt => exact absurd hQ_lt (not_lt.mpr hQ_ge)
