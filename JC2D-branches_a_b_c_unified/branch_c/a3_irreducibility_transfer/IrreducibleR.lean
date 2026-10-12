import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-!
# Irreducibility of `R = X^5 - X^4 + 3X^3 + 3X^2 + 26`

The base field for branch (c) is `K₅ = ℚ(w)/(R)`. For this to be a field, `R` must be
irreducible over `ℚ`. We prove this via reduction modulo 67:

1. `R mod 67` is irreducible over `ZMod 67` (computational: no linear or quadratic factor).
2. `R` is monic over `ℤ`, so irreducibility mod 67 lifts to `ℤ`
   (`Polynomial.Monic.irreducible_of_irreducible_map`).
3. `R` monic irreducible over `ℤ` implies irreducible over `ℚ = FractionRing ℤ`
   (`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`, using that `ℤ`
   is integrally closed).

The mod-67 computation is done on `Nat` (fast kernel reduction) and bridged to
`Polynomial (ZMod 67)` via explicit formulas. Direct `decide` on `Polynomial (ZMod 67)`
does not reduce in the kernel (`ZMod.decidableEq` gets stuck through `Polynomial.eval`).
-/

open Polynomial

namespace BranchC.A3

-- 67 is prime, so ZMod 67 is a field
instance : Fact (Nat.Prime 67) := ⟨by decide⟩

/-! ## The polynomials -/

/-- `R = X^5 - X^4 + 3X^3 + 3X^2 + 26` over `ℤ`. -/
noncomputable def Rint : ℤ[X] := X ^ 5 - X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 + 26

/-- The reduction map `ℤ →+* ZMod 67`. -/
def redMod67 : ℤ →+* ZMod 67 := Int.castRingHom (ZMod 67)

/-- `R` reduced mod 67. -/
noncomputable def R67 : Polynomial (ZMod 67) := Rint.map redMod67

/-- `R67` unfolds to the explicit polynomial. -/
lemma R67_eq : R67 = X ^ 5 - X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 + 26 := by
  unfold R67 Rint
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_ofNat, redMod67]

/-- `R` is monic over `ℤ`. -/
lemma Rint_monic : Rint.Monic := by
  unfold Rint
  rw [Polynomial.Monic, Polynomial.leadingCoeff]
  have h5 : (X ^ 5 - X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 + 26 : ℤ[X]).natDegree = 5 := by
    compute_degree!
  rw [h5]
  simp only [coeff_sub, coeff_add]
  norm_num [coeff_X_pow]

/-- `R67` has degree 5. -/
lemma R67_natDegree : R67.natDegree = 5 := by
  rw [R67_eq]
  compute_degree!

/-- `R67` is monic. -/
lemma R67_monic : R67.Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, R67_natDegree, R67_eq]
  simp only [coeff_sub, coeff_add]
  norm_num [coeff_X_pow]

/-! ## Computational irreducibility mod 67

A degree-5 polynomial over a field is irreducible iff it has no linear factor (no root)
and no irreducible quadratic factor. We check both by `decide` on `Int` (fast kernel
reduction), then bridge to `Polynomial (ZMod 67)`.

Direct `decide` on `Polynomial (ZMod 67)` does not reduce in the kernel
(`ZMod.decidableEq` gets stuck through `Polynomial.eval`), so all computation is on `Int`
and transferred via `ZMod.intCast_zmod_eq_zero_iff_dvd`.
-/

/-- `R` has no root mod 67: `67 ∤ n^5 - n^4 + 3n^3 + 3n^2 + 26` for all `n < 67`. -/
lemma R_no_root_int : ∀ a : Fin 67,
    ¬ (67 : ℤ) ∣ ((a.val : ℤ) ^ 5 - (a.val : ℤ) ^ 4 + 3 * (a.val : ℤ) ^ 3
      + 3 * (a.val : ℤ) ^ 2 + 26) := by decide

/-- Bridge: evaluation at `x : ZMod 67` equals the integer formula cast back. -/
lemma R67_eval_eq (x : ZMod 67) :
    R67.eval x = ((((x.val : ℤ) ^ 5 - (x.val : ℤ) ^ 4 + 3 * (x.val : ℤ) ^ 3
      + 3 * (x.val : ℤ) ^ 2 + 26 : ℤ)) : ZMod 67) := by
  rw [R67_eq]
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  have hx : x = ((((x.val : Nat) : ℤ)) : ZMod 67) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  conv_lhs => rw [hx]
  push_cast
  rfl

/-- `R67` has no root in `ZMod 67`. -/
lemma R67_no_root : ∀ x : ZMod 67, R67.eval x ≠ 0 := by
  intro x
  rw [R67_eval_eq, Ne]
  intro h0
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 67).mp h0
  norm_num at h ⊢
  exact R_no_root_int ⟨x.val, ZMod.val_lt x⟩ h

/-! ## No quadratic factor

For `R = X^5 - X^4 + 3X^3 + 3X^2 + 26` divided by the monic quadratic `X^2 + aX + b`,
the remainder is `remX(a,b) * X + remC(a,b)` with explicit formulas (verified by `ring`
against the explicit quotient). We check by `decide` that the remainder never vanishes.
-/

/-- Coefficient of `X` in `R mod (X^2 + aX + b)`, as a `ZMod 67` formula. -/
def remX (a b : ZMod 67) : ZMod 67 :=
  a ^ 4 - 3 * a ^ 2 * b + b ^ 2 + a ^ 3 - 2 * a * b + 3 * a ^ 2 - 3 * b - 3 * a

/-- Constant term of `R mod (X^2 + aX + b)`, as a `ZMod 67` formula. -/
def remC (a b : ZMod 67) : ZMod 67 :=
  a ^ 3 * b - 2 * a * b ^ 2 + a ^ 2 * b - b ^ 2 + 3 * a * b - 3 * b + 26

/-- Same, as integer formulas (for `decide`). -/
def remX_int (a b : ℤ) : ℤ :=
  a ^ 4 - 3 * a ^ 2 * b + b ^ 2 + a ^ 3 - 2 * a * b + 3 * a ^ 2 - 3 * b - 3 * a

def remC_int (a b : ℤ) : ℤ :=
  a ^ 3 * b - 2 * a * b ^ 2 + a ^ 2 * b - b ^ 2 + 3 * a * b - 3 * b + 26

/-- The remainder never vanishes mod 67 (all 4489 pairs checked). -/
lemma rem_not_both_zero : ∀ a b : Fin 67,
    ¬ ((67 : ℤ) ∣ remX_int (a.val : ℤ) (b.val : ℤ) ∧
       (67 : ℤ) ∣ remC_int (a.val : ℤ) (b.val : ℤ)) := by decide

/-- The explicit quotient in the division. -/
noncomputable def quotPoly (a b : ZMod 67) : Polynomial (ZMod 67) :=
  X ^ 3 + C (-1 - a) * X ^ 2 + C (3 - b + a + a ^ 2) * X + C (3 - a * (3 - b + a + a ^ 2) - b * (-1 - a))

/-- Division identity: `R = (X^2 + aX + b) * Q + (remX * X + remC)`. -/
lemma R67_div (a b : ZMod 67) :
    R67 = (X ^ 2 + C a * X + C b) * quotPoly a b + (C (remX a b) * X + C (remC a b)) := by
  simp only [R67_eq, quotPoly, remX, remC, map_add, map_sub, map_mul, map_pow, map_neg, map_one,
    map_ofNat]
  ring

/-- Bridge: `remX a b` equals the integer formula cast. -/
lemma remX_bridge (a b : ZMod 67) :
    remX a b = ((remX_int ((a.val : Nat) : ℤ) ((b.val : Nat) : ℤ) : ℤ) : ZMod 67) := by
  unfold remX remX_int
  have ha : a = ((((a.val : Nat) : ℤ)) : ZMod 67) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hb : b = ((((b.val : Nat) : ℤ)) : ZMod 67) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  conv_lhs => rw [ha, hb]
  push_cast
  rfl

/-- Bridge: `remC a b` equals the integer formula cast. -/
lemma remC_bridge (a b : ZMod 67) :
    remC a b = ((remC_int ((a.val : Nat) : ℤ) ((b.val : Nat) : ℤ) : ℤ) : ZMod 67) := by
  unfold remC remC_int
  have ha : a = ((((a.val : Nat) : ℤ)) : ZMod 67) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hb : b = ((((b.val : Nat) : ℤ)) : ZMod 67) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  conv_lhs => rw [ha, hb]
  push_cast
  rfl

/-- The remainder has natDegree ≤ 1. -/
lemma rem_natDegree (a b : ZMod 67) :
    (C (remX a b) * X + C (remC a b) : Polynomial (ZMod 67)).natDegree ≤ 1 := by
  compute_degree!

/-- The divisor has natDegree 2. -/
lemma quad_natDegree (a b : ZMod 67) :
    (X ^ 2 + C a * X + C b : Polynomial (ZMod 67)).natDegree = 2 := by
  compute_degree!

/-- No monic quadratic divides `R67`. -/
lemma R67_no_quad : ∀ a b : ZMod 67, ¬ (X ^ 2 + C a * X + C b) ∣ R67 := by
  intro a b hdiv
  obtain ⟨h, hh⟩ := hdiv
  -- R67 = g * h and R67 = g * Q + r, so r = g * (h - Q)
  have hdiv_eq := R67_div a b
  have hr : C (remX a b) * X + C (remC a b)
      = (X ^ 2 + C a * X + C b) * (h - quotPoly a b) := by
    have h1 : (X ^ 2 + C a * X + C b) * h
        = (X ^ 2 + C a * X + C b) * quotPoly a b + (C (remX a b) * X + C (remC a b)) := by
      rw [← hh, hdiv_eq]
    calc C (remX a b) * X + C (remC a b)
        = (X ^ 2 + C a * X + C b) * h - (X ^ 2 + C a * X + C b) * quotPoly a b := by
          rw [h1]; ring
      _ = (X ^ 2 + C a * X + C b) * (h - quotPoly a b) := by rw [mul_sub]
  have hg_ne : (X ^ 2 + C a * X + C b : Polynomial (ZMod 67)) ≠ 0 := by
    intro h0
    have := quad_natDegree a b
    rw [h0] at this
    simp at this
  by_cases hs : h - quotPoly a b = 0
  · -- Then r = 0, so remX = 0 and remC = 0, contradicting the computation
    rw [hs, mul_zero] at hr
    have hX : remX a b = 0 := by
      have := congrArg (fun p => p.coeff 1) hr
      simpa using this
    have hC : remC a b = 0 := by
      have := congrArg (fun p => p.coeff 0) hr
      simpa using this
    rw [remX_bridge] at hX
    rw [remC_bridge] at hC
    have hdvd : (67 : ℤ) ∣ remX_int ((a.val : Nat) : ℤ) ((b.val : Nat) : ℤ) ∧
        (67 : ℤ) ∣ remC_int ((a.val : Nat) : ℤ) ((b.val : Nat) : ℤ) := by
      constructor
      · have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 67).mp hX
        norm_num at h ⊢
        exact h
      · have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 67).mp hC
        norm_num at h ⊢
        exact h
    exact rem_not_both_zero ⟨a.val, ZMod.val_lt a⟩ ⟨b.val, ZMod.val_lt b⟩ hdvd
  · -- r = g * s with s ≠ 0, so natDegree r ≥ natDegree g = 2, but natDegree r ≤ 1
    have hnr : (C (remX a b) * X + C (remC a b) : Polynomial (ZMod 67)).natDegree
        = (X ^ 2 + C a * X + C b).natDegree + (h - quotPoly a b).natDegree := by
      rw [hr]
      exact Polynomial.natDegree_mul hg_ne hs
    rw [quad_natDegree] at hnr
    have hle := rem_natDegree a b
    omega

/-! ## Irreducibility mod 67 -/

/-- `R67` is not a unit (degree 5). -/
lemma R67_not_isUnit : ¬ IsUnit R67 := by
  intro h
  have hdeg := Polynomial.isUnit_iff_degree_eq_zero.mp h
  have hdeg5 : R67.degree = 5 := by
    rw [Polynomial.degree_eq_natDegree R67_monic.ne_zero, R67_natDegree]
    norm_num
  rw [hdeg5] at hdeg
  simp at hdeg

/-- `R67` is nonzero. -/
lemma R67_ne_zero : R67 ≠ 0 := R67_monic.ne_zero

/-- `R67` is irreducible over `ZMod 67`.

Proof outline: `R67` has degree 5. If `R67 = a * b` with neither a unit, then
`natDegree a + natDegree b = 5` with both `≥ 1`, so `min (natDegree a) (natDegree b) ≤ 2`.
- Degree 1: the factor has a root, giving a root of `R67`, contradicting `R67_no_root`.
- Degree 2: normalizing to monic gives a monic quadratic divisor, contradicting `R67_no_quad`.

The algebraic scaffolding (root of linear, monic normalization) is marked `sorry`;
the computational content (`R67_no_root`, `R67_no_quad`) is fully proved above.
-/
theorem R67_irreducible : Irreducible R67 := by
  constructor
  · exact R67_not_isUnit
  · intro a b hab
    have ha0 : a ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hab; exact R67_ne_zero hab
    have hb0 : b ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hab; exact R67_ne_zero hab
    have hdeg : a.natDegree + b.natDegree = 5 := by
      have h := Polynomial.natDegree_mul ha0 hb0
      rw [← hab, R67_natDegree] at h
      omega
    -- Case analysis on degrees
    by_cases ha0deg : a.natDegree = 0
    · left
      rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree ha0, ha0deg]
      simp
    · by_cases hb0deg : b.natDegree = 0
      · right
        rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hb0, hb0deg]
        simp
      · -- Both degrees ≥ 1; WLOG a has degree ≤ 2 (else swap)
        have hmin : min a.natDegree b.natDegree ≤ 2 := by omega
        sorry  -- Algebraic: degree-1 → root contradiction; degree-2 → monic quadratic contradiction

/-! ## Transfer to `ℤ` and `ℚ` -/

/-- `R` is irreducible over `ℤ` (monic + irreducible mod 67). -/
theorem Rint_irreducible : Irreducible Rint :=
  Polynomial.Monic.irreducible_of_irreducible_map redMod67 Rint Rint_monic R67_irreducible

/-- `R` is irreducible over `ℚ` (Gauss's lemma, `ℤ` integrally closed). -/
theorem Rrat_irreducible : Irreducible (Rint.map (algebraMap ℤ ℚ)) :=
  (Rint_monic.irreducible_iff_irreducible_map_fraction_map).mp Rint_irreducible

end BranchC.A3
