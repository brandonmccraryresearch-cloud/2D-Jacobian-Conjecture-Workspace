import GradeA.Chart.Terms
import GradeA.Macaulay

/-!
# The chart generators as polynomials over `ℤ[X]` (branch (c), step A2.0)

The Macaulay argument (`GradeA.Macaulay`, `no_common_zero_of_certificate`) takes the generators as
`MvPolynomial (Fin 5) ℤ[X]`: polynomials in the chart variables t s r u q whose coefficients are polynomials in `X`,
the symbol for the root `w` of `R`. `polyOfTerms` builds that form from the same term lists as the reflected
expressions of `GradeA.Chart.Gens`, and `denote_exprOfTerms_chartCtx` says the two agree at every chart point:
the expression at the chart context equals `evalAt w z` of the polynomial, with `z = (b₁₁,₂₀, b₁₁,₂₁, a₆,₁₃, a₇,₁₅,
b₁₀,₂₁)`.
-/

namespace BranchC.GradeA.Chart
open Lean.Grind.CommRing BranchAb.ChartProof

/-- The monomial `t^et s^es r^er u^eu q^eq` of a term. -/
noncomputable def Term.mono (t : Term) : Fin 5 →₀ ℕ :=
  Finsupp.single 0 t.et + Finsupp.single 1 t.es + Finsupp.single 2 t.er + Finsupp.single 3 t.eu +
    Finsupp.single 4 t.eq

/-- The coefficient `c · X^i ∈ ℤ[X]` of a term. -/
noncomputable def Term.coeffX (t : Term) : Polynomial ℤ := Polynomial.C t.c * Polynomial.X ^ t.i

/-- The term as a polynomial over `ℤ[X]`. -/
noncomputable def Term.poly (t : Term) : MvPolynomial (Fin 5) (Polynomial ℤ) :=
  MvPolynomial.monomial t.mono t.coeffX

/-- The sum of a list of terms, as a polynomial over `ℤ[X]`. -/
noncomputable def polyOfTerms (l : List Term) : MvPolynomial (Fin 5) (Polynomial ℤ) := (l.map Term.poly).sum

theorem evalAt_termPoly {L : Type*} [CommRing L] (w : L) (z : Fin 5 → L) (t : Term) :
    evalAt w z t.poly = (t.c : L) * w ^ t.i * z 0 ^ t.et * z 1 ^ t.es * z 2 ^ t.er * z 3 ^ t.eu * z 4 ^ t.eq := by
  unfold evalAt Term.poly Term.coeffX Term.mono
  rw [MvPolynomial.eval₂_monomial]
  have hz : ∀ (i : Fin 5), z i ^ 0 = 1 := fun _ => pow_zero _
  have hadd : ∀ (i : Fin 5) (a b : ℕ), z i ^ (a + b) = z i ^ a * z i ^ b := fun _ _ _ => pow_add _ _ _
  rw [Finsupp.prod_add_index' hz hadd, Finsupp.prod_add_index' hz hadd, Finsupp.prod_add_index' hz hadd,
    Finsupp.prod_add_index' hz hadd, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow]
  simp only [Finsupp.prod_single_index, pow_zero, eq_intCast]
  ring

theorem evalAt_polyOfTerms {L : Type*} [CommRing L] (w : L) (z : Fin 5 → L) (l : List Term) :
    evalAt w z (polyOfTerms l) =
      (l.map fun t => (t.c : L) * w ^ t.i * z 0 ^ t.et * z 1 ^ t.es * z 2 ^ t.er * z 3 ^ t.eu * z 4 ^ t.eq).sum := by
  induction l with
  | nil => simp [polyOfTerms, evalAt]
  | cons t l ih =>
    have h := ih
    simp only [polyOfTerms, List.map_cons, List.sum_cons] at h ⊢
    rw [← evalAt_termPoly, ← h]
    unfold evalAt
    rw [MvPolynomial.eval₂_add]

/-- **The bridge:** at a chart point, the reflected expression of a term list equals `evalAt` of its polynomial. -/
theorem denote_exprOfTerms_chartCtx {L : Type*} [CommRing L]
    (w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21 : L) (l : List Term) :
    (exprOfTerms l).denote (chartCtx w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21) =
      evalAt w ![b_11_20, b_11_21, a_6_13, a_7_15, b_10_21] (polyOfTerms l) := by
  rw [denote_exprOfTerms, evalAt_polyOfTerms]
  congr 1

end BranchC.GradeA.Chart
