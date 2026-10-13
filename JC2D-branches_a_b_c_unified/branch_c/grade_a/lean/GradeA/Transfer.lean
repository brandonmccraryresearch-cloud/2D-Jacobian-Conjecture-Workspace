import GradeA.IrreducibleR

/-!
# The transfer from `𝔽_p` to characteristic 0, through `ℤ[X]`

Branch (c), corrected step A3 (review of 2026-10-12, §4.3, steps 4–5).

The rank computation of branch (c) happens modulo `p = 32003` at a root `w₀` of `R`; the statement to prove
(`ChartEmptyC_T1ne0 L`) is about a root `w` of `R` in an arbitrary field `L` of characteristic 0. There is no ring
map between the two (characteristic 0 → characteristic `p`), so the transfer must go through a ring that maps to
both. That ring is `ℤ[X]`: `X ↦ w` and `X ↦ w₀`.

* `eval_eq_zero_of_eval_root`: if `D ∈ ℤ[X]` vanishes at a root `w` of `R` in a field of characteristic 0, then
  `R ∣ D` in `ℤ[X]` (`R` is the minimal polynomial of `w`, and is monic), so `D` vanishes at every root `w₀` of `R`
  in every commutative ring.
* `no_left_kernel`: let `M` be a square matrix over `ℤ[X]` (in the application, the pivot block of the Macaulay
  matrix, with entries polynomial in the root). If `M(w₀)` has a left inverse modulo `p`, then `M(w)` has no nonzero
  left kernel vector over `L`. Proof: `det M ∈ ℤ[X]`; `det M(w) = 0` by the kernel vector; so `det M(w₀) = 0` by
  the transfer; but `det M(w₀)` is a unit.

In the application the kernel vector is `v = (μ(z))_μ`, the values of the row monomials at a common zero `z` of the
chart generators, with `v₁ = 1` for the monomial `1`. Nothing here depends on the size of `M`.
-/

open Polynomial Matrix

namespace BranchC.GradeA

/-- **Transfer through `ℤ[X]`.** A polynomial with integer coefficients that vanishes at a root of `R` in a field of
characteristic 0 vanishes at every root of `R` in every commutative ring. -/
theorem eval_eq_zero_of_eval_root {L : Type*} [Field L] [CharZero L] (w : L)
    (hw : eval₂ (Int.castRingHom L) w Rint = 0) (D : ℤ[X]) (hD : eval₂ (Int.castRingHom L) w D = 0)
    {S : Type*} [CommRing S] (w₀ : S) (hw₀ : eval₂ (Int.castRingHom S) w₀ Rint = 0) :
    eval₂ (Int.castRingHom S) w₀ D = 0 := by
  have hwQ : aeval w Rrat = 0 := by
    rw [← Rint_map_rat, aeval_map_algebraMap, aeval_def, algebraMap_int_eq]; exact hw
  have hDQ : aeval w (D.map (algebraMap ℤ ℚ)) = 0 := by
    rw [aeval_map_algebraMap, aeval_def, algebraMap_int_eq]; exact hD
  have h1 : Rrat ∣ D.map (algebraMap ℤ ℚ) := Rrat_dvd_of_aeval_eq_zero w hwQ _ hDQ
  have h2 : (D %ₘ Rint).map (algebraMap ℤ ℚ) = 0 := by
    rw [map_modByMonic _ Rint_monic, Rint_map_rat]
    exact (modByMonic_eq_zero_iff_dvd Rrat_monic).mpr h1
  have h3 : D %ₘ Rint = 0 :=
    Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int (by rw [h2, Polynomial.map_zero])
  obtain ⟨Q, rfl⟩ := (modByMonic_eq_zero_iff_dvd Rint_monic).mp h3
  rw [eval₂_mul, hw₀, zero_mul]

/-- **No left kernel.** If the pivot block `M ∈ Mat_n(ℤ[X])` has a left inverse at a root `w₀` of `R` in `ZMod p`,
then at a root `w` of `R` in a field `L` of characteristic 0 it has no nonzero vector `v` with `v ᵥ* M(w) = 0`. -/
theorem no_left_kernel {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℤ[X])
    {p : ℕ} [Fact p.Prime] (w₀ : ZMod p) (hw₀ : eval₂ (Int.castRingHom (ZMod p)) w₀ Rint = 0)
    (Cinv : Matrix n n (ZMod p))
    (hC : Cinv * (eval₂RingHom (Int.castRingHom (ZMod p)) w₀).mapMatrix M = 1)
    {L : Type*} [Field L] [CharZero L] (w : L) (hw : eval₂ (Int.castRingHom L) w Rint = 0)
    (v : n → L) (hv : v ≠ 0) (hker : v ᵥ* (eval₂RingHom (Int.castRingHom L) w).mapMatrix M = 0) :
    False := by
  have hdetL : ((eval₂RingHom (Int.castRingHom L) w).mapMatrix M).det = 0 :=
    Matrix.exists_vecMul_eq_zero_iff.mp ⟨v, hv, hker⟩
  rw [← RingHom.map_det, coe_eval₂RingHom] at hdetL
  have hdetp := eval_eq_zero_of_eval_root w hw M.det hdetL w₀ hw₀
  have hunit : ((eval₂RingHom (Int.castRingHom (ZMod p)) w₀).mapMatrix M).det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hC
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h
    exact zero_ne_one h
  rw [← RingHom.map_det, coe_eval₂RingHom] at hunit
  exact hunit hdetp

end BranchC.GradeA
