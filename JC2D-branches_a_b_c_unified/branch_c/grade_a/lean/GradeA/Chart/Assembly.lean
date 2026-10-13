import GradeA.Chart.Main
import GradeA.Chart.Poly
import Jacobian.BranchC.T1Zero.Combine

/-!
# Branch (c): `ChartEmptyC_T1ne0` from the two finite deliverables A1 and A2 (the interface)

`chartEmptyC_T1ne0_of_certificate` proves the open premise of branch (c), `ChartEmptyC_T1ne0 L` for every field `L`
of characteristic 0 (Jacobian/BranchC/T1Zero/Combine.lean), from hypotheses that are finite computations on concrete
data:

* **the Macaulay data:** rows `mon : ρ → monomials` (injective, containing `1`), and pivot columns given by a generator
  `gen c` and a multiplier `mult c`, such that every monomial of `mult c · F_{gen c}` is a row (`hsupp`);
* **A1:** `Cinv * MS = 1` over `ZMod p`: the kernel-checked packed certificate of `rank_lemma_check/` is a left inverse
  of the pivot block `MS` written in its data;
* **A2:** `MS` is the pivot block of the Macaulay matrix of the chart generators `Fpoly`, evaluated at `w₀ mod p`, up
  to a nonzero scale per generator (`hA2`). The scales are needed because the rank check used the generators unscaled,
  while `Fpoly` are the integral generators `Dk^d · D_n · cond_n|chart` (`grade_a/certgen/gen_chart.py` checks
  `Fpoly_n(w₀) = Dk^d D_n · G_n mod p` at both primes of the rank check).

The proof combines the chart reduction (`chart_gens_vanish`, kernel-checked: a chart point is a common zero of the
six generators), the bridge to `MvPolynomial` form (`denote_exprOfTerms_chartCtx`), and the Macaulay argument with
the transfer through `ℤ[X]` (`no_common_zero_of_certificate`). Nothing else is assumed: the hypotheses `b₁₁,₂₀ ≠ 0` and
the five "pure" conditions of `ChartEmptyC_T1ne0` are not used.
-/

namespace BranchC.GradeA.Chart
open Lean.Grind.CommRing BranchAb.ChartProof Polynomial Matrix

/-- The six chart generators as polynomials over `ℤ[X]` (order Ψ, Φ₁, Φ₂, Θ₁, Θ₂, Θ₃). -/
noncomputable def Fpoly : Fin 6 → MvPolynomial (Fin 5) ℤ[X]
  | 0 => polyOfTerms tl_Psi
  | 1 => polyOfTerms tl_Phi1
  | 2 => polyOfTerms tl_Phi2
  | 3 => polyOfTerms tl_Theta1
  | 4 => polyOfTerms tl_Theta2
  | 5 => polyOfTerms tl_Theta3

/-- **The chart reduction in `MvPolynomial` form.** A chart point is a common zero of the six generators at
`z = (b₁₁,₂₀, b₁₁,₂₁, a₆,₁₃, a₇,₁₅, b₁₀,₂₁)`. -/
theorem Fpoly_vanish {L : Type*} [Field L] [CharZero L] (w : L)
    (hw : w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 = 0)
    (b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21 : L) (ht2 : b_12_22 = 1)
    (c_Omega : cond_Omega w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21 = 0)
    (c_Psi : cond_Psi w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21 = 0)
    (c_Phi1 : cond_Phi1 w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21 = 0)
    (c_Phi2 : cond_Phi2 w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21 = 0)
    (c_Theta1 : cond_Theta1 w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21 = 0)
    (c_Theta2 : cond_Theta2 w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21 = 0)
    (c_Theta3 : cond_Theta3 w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21 = 0) :
    ∀ n, evalAt w ![b_11_20, b_11_21, a_6_13, a_7_15, b_10_21] (Fpoly n) = 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := chart_gens_vanish w hw b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21
    ht2 c_Omega c_Psi c_Phi1 c_Phi2 c_Theta1 c_Theta2 c_Theta3
  have key : ∀ l : List Term,
      (exprOfTerms l).denote (chartCtx w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21) = 0 →
      evalAt w ![b_11_20, b_11_21, a_6_13, a_7_15, b_10_21] (polyOfTerms l) = 0 := fun l h => by
    rw [← denote_exprOfTerms_chartCtx w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21]; exact h
  intro n
  fin_cases n
  · exact key tl_Psi h0
  · exact key tl_Phi1 h1
  · exact key tl_Phi2 h2
  · exact key tl_Theta1 h3
  · exact key tl_Theta2 h4
  · exact key tl_Theta3 h5

/-- `R` at a point of any commutative ring, written out. -/
theorem eval₂_Rint {S : Type*} [CommRing S] (x : S) :
    eval₂ (Int.castRingHom S) x Rint = x ^ 5 - x ^ 4 + 3 * x ^ 3 + 3 * x ^ 2 + 26 := by
  simp [Rint]

/-- **The interface.** The Macaulay data, A1 and A2 give `ChartEmptyC_T1ne0 L` for every field of characteristic 0. -/
theorem chartEmptyC_T1ne0_of_certificate {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (mon : ρ → Fin 5 →₀ ℕ) (hmon : Function.Injective mon) (r₁ : ρ) (hr₁ : mon r₁ = 0)
    (gen : ρ → Fin 6) (mult : ρ → Fin 5 →₀ ℕ)
    (hsupp : ∀ c, ∀ d ∈ (MvPolynomial.monomial (mult c) (1 : ℤ[X]) * Fpoly (gen c)).support, d ∈ Set.range mon)
    {p : ℕ} [Fact p.Prime] (w₀ : ZMod p) (hw₀ : eval₂ (Int.castRingHom (ZMod p)) w₀ Rint = 0)
    (MS Cinv : Matrix ρ ρ (ZMod p)) (scale : Fin 6 → ZMod p) (hscale : ∀ n, scale n ≠ 0)
    (hA1 : Cinv * MS = 1)
    (hA2 : (eval₂RingHom (Int.castRingHom (ZMod p)) w₀).mapMatrix (macaulay Fpoly mon gen mult) =
      MS * Matrix.diagonal (fun c => scale (gen c)))
    (L : Type*) [Field L] [CharZero L] : ChartEmptyC_T1ne0 L := by
  intro w hw b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21 ht2 _ cO cPsi cPhi1 cPhi2 cT1 cT2 cT3 _ _ _ _ _
  have hz := Fpoly_vanish w hw b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21 ht2 cO cPsi cPhi1 cPhi2 cT1
    cT2 cT3
  have hwR : eval₂ (Int.castRingHom L) w Rint = 0 := by rw [eval₂_Rint]; exact hw
  refine no_common_zero_of_certificate Fpoly mon hmon r₁ hr₁ gen mult hsupp w₀ hw₀
    (Matrix.diagonal (fun c => (scale (gen c))⁻¹) * Cinv) ?_ w hwR _ hz
  rw [hA2, Matrix.mul_assoc, ← Matrix.mul_assoc Cinv, hA1, Matrix.one_mul, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext c
  exact inv_mul_cancel₀ (hscale (gen c))

end BranchC.GradeA.Chart
