import GradeA.Transfer

/-!
# The Macaulay argument, generically: no common zero from a modular certificate

Branch (c), corrected steps A2–A5 (review of 2026-10-12, §4.3, step 3 and the assembly).

Let `F₁, …, F_k ∈ ℤ[X][z]` (`MvPolynomial σ ℤ[X]`): polynomials in the chart variables `z`, whose coefficients are
polynomials in `X`, the symbol for the root `w` of `R`. Fix

* rows: monomials `mon r` (`r : ρ`), injective, with `mon r₁ = 1` for some row `r₁`;
* columns (as many as rows: this is the square pivot block): a generator `gen c` and a multiplier monomial
  `mult c`, such that every monomial of `mult c · F_{gen c}` is a row.

The block is `M r c = coeff_{mon r} (mult c · F_{gen c}) ∈ ℤ[X]` (`macaulay`).

* `macaulay_vecMul_eq_zero`: if `z ∈ L^σ` is a common zero of the `F_n` at `X = w`, the row vector of monomial values
  `v_r = (mon r)(z)` satisfies `v ᵥ* M(w) = 0`, because `Σ_r v_r · M r c (w) = (mult c · F_{gen c})(w; z) = 0`.
* `no_common_zero_of_certificate`: if moreover `M(w₀)` has a left inverse modulo a prime `p` at a root `w₀` of `R`,
  then the `F_n` have no common zero at any root `w` of `R` in any field of characteristic 0 (`v ≠ 0` since
  `v_{r₁} = 1`; then `no_left_kernel`).

Everything here is generic. What remains for `ChartEmptyC_T1ne0` is to supply the concrete data: the six chart
generators `F_n` with the proof that a chart point gives a common zero (steps 1–2 of the review's §4.3), the 3199
rows and pivot columns with the support condition, and the left inverse modulo 32003 (the kernel-checked packed
identities of `branch_c/rank_lemma_check/`, connected to `macaulay`).
-/

open Polynomial Matrix

namespace BranchC.GradeA

variable {σ : Type*} [Fintype σ]

/-- `G(w; z)`: the coefficients (polynomials in `X`) evaluated at `w`, the variables at `z`. -/
noncomputable def evalAt {L : Type*} [CommRing L] (w : L) (z : σ → L) (G : MvPolynomial σ ℤ[X]) : L :=
  MvPolynomial.eval₂ (eval₂RingHom (Int.castRingHom L) w) z G

/-- The value of the monomial `d` at `z`. -/
noncomputable def monVal {L : Type*} [CommRing L] (z : σ → L) (d : σ →₀ ℕ) : L := ∏ i, z i ^ d i

/-- The Macaulay block: entry `(r, c)` is the coefficient of the row monomial `mon r` in `mult c · F_{gen c}`. -/
noncomputable def macaulay {ρ κ : Type*} {k : ℕ} (F : Fin k → MvPolynomial σ ℤ[X]) (mon : ρ → σ →₀ ℕ)
    (gen : κ → Fin k) (mult : κ → σ →₀ ℕ) : Matrix ρ κ ℤ[X] :=
  fun r c => (MvPolynomial.monomial (mult c) (1 : ℤ[X]) * F (gen c)).coeff (mon r)

/-- Evaluation as a sum over the rows, when the rows contain the support. -/
lemma evalAt_eq_sum_rows {ρ : Type*} [Fintype ρ] {L : Type*} [CommRing L] (mon : ρ → σ →₀ ℕ)
    (hmon : Function.Injective mon) (G : MvPolynomial σ ℤ[X]) (hsupp : ∀ d ∈ G.support, d ∈ Set.range mon)
    (w : L) (z : σ → L) :
    evalAt w z G = ∑ r, monVal z (mon r) * eval₂ (Int.castRingHom L) w (G.coeff (mon r)) := by
  classical
  unfold evalAt monVal
  rw [MvPolynomial.eval₂_eq']
  have himage : G.support ⊆ Finset.univ.image mon := by
    intro d hd
    obtain ⟨r, rfl⟩ := hsupp d hd
    exact Finset.mem_image_of_mem _ (Finset.mem_univ r)
  rw [Finset.sum_subset himage (fun d _ hd => by
        rw [MvPolynomial.notMem_support_iff.mp hd, map_zero, zero_mul])]
  rw [Finset.sum_image (fun r _ r' _ h => hmon h)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [coe_eval₂RingHom, mul_comm]

/-- **Left kernel at a common zero.** -/
theorem macaulay_vecMul_eq_zero {ρ : Type*} [Fintype ρ] [DecidableEq ρ] {k : ℕ} {L : Type*} [CommRing L]
    (F : Fin k → MvPolynomial σ ℤ[X]) (mon : ρ → σ →₀ ℕ) (hmon : Function.Injective mon)
    (gen : ρ → Fin k) (mult : ρ → σ →₀ ℕ)
    (hsupp : ∀ c, ∀ d ∈ (MvPolynomial.monomial (mult c) (1 : ℤ[X]) * F (gen c)).support, d ∈ Set.range mon)
    (w : L) (z : σ → L) (hz : ∀ n, evalAt w z (F n) = 0) :
    (fun r => monVal z (mon r)) ᵥ* (eval₂RingHom (Int.castRingHom L) w).mapMatrix (macaulay F mon gen mult) = 0 := by
  funext c
  have h := evalAt_eq_sum_rows mon hmon _ (hsupp c) w z
  have hzero : evalAt w z (MvPolynomial.monomial (mult c) (1 : ℤ[X]) * F (gen c)) = 0 := by
    unfold evalAt
    rw [MvPolynomial.eval₂_mul]
    have := hz (gen c)
    unfold evalAt at this
    rw [this, mul_zero]
  rw [hzero] at h
  simp only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, Pi.zero_apply,
    coe_eval₂RingHom]
  exact h.symm

/-- **No common zero, from a modular certificate.** -/
theorem no_common_zero_of_certificate {ρ : Type*} [Fintype ρ] [DecidableEq ρ] {k : ℕ}
    (F : Fin k → MvPolynomial σ ℤ[X]) (mon : ρ → σ →₀ ℕ) (hmon : Function.Injective mon)
    (r₁ : ρ) (hr₁ : mon r₁ = 0) (gen : ρ → Fin k) (mult : ρ → σ →₀ ℕ)
    (hsupp : ∀ c, ∀ d ∈ (MvPolynomial.monomial (mult c) (1 : ℤ[X]) * F (gen c)).support, d ∈ Set.range mon)
    {p : ℕ} [Fact p.Prime] (w₀ : ZMod p) (hw₀ : eval₂ (Int.castRingHom (ZMod p)) w₀ Rint = 0)
    (Cinv : Matrix ρ ρ (ZMod p))
    (hC : Cinv * (eval₂RingHom (Int.castRingHom (ZMod p)) w₀).mapMatrix (macaulay F mon gen mult) = 1)
    {L : Type*} [Field L] [CharZero L] (w : L) (hw : eval₂ (Int.castRingHom L) w Rint = 0)
    (z : σ → L) (hz : ∀ n, evalAt w z (F n) = 0) : False := by
  refine no_left_kernel (macaulay F mon gen mult) w₀ hw₀ Cinv hC w hw (fun r => monVal z (mon r)) ?_
    (macaulay_vecMul_eq_zero F mon hmon gen mult hsupp w z hz)
  intro h0
  have h1 := congrFun h0 r₁
  simp [hr₁, monVal] at h1

end BranchC.GradeA
