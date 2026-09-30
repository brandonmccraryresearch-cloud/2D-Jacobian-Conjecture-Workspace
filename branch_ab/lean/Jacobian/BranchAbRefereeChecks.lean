import Mathlib

open Polynomial

/-!
# Branch (a), (b) elimination: referee checks

Companion to `Jacobian.BranchAbObstruction`.  Nothing here is assumed; every
statement is proved from Mathlib.

1. `t_zero_case_char`: the §8.3 step with its sharp hypotheses `(2 : K) ≠ 0` and
   `(12 : K) ≠ 0`, i.e. `char K ∉ {2, 3}`.  `CharZero` (as in `t_zero_case`) is
   sufficient but not necessary.
2. `t_zero_case_fails_char3`: in characteristic 3 the hypotheses of the §8.3 step are
   satisfiable, so the argument is valid in every characteristic other than 2 and 3,
   not in every characteristic.
3. `minor_vanish`: if `b + s₁ M + s₂ L = 0` row by row, every 3×3 minor
   `det[b | M | L]` on rows `i, j, k` vanishes (the implication §8.4 uses).
4. `no_nonzero_direction`: the §8.4 argument end to end.  If the seven E₂ conditions
   are solvable in `(s₁, s₂)` at `t`, and `t₁⁵`, `t₂⁵` are `K`-linear combinations
   (coefficients `c₀`, `c₁`) of the 3×3 minor polynomials, then `t = 0`.  The only
   inputs left unformalized are the computed `b, M, L` and the vectors `c₀, c₁`.
-/

/-- §8.3 final step with its true characteristic hypothesis. -/
theorem t_zero_case_char {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h12 : (12 : K) ≠ 0)
    (A₂ B₀ : K[X]) (hA : A₂ ≠ 0)
    (hE2 : (2 : K[X]) * A₂ * derivative B₀ = 0)
    (hvertex : B₀.coeff 12 ≠ 0) : False := by
  have h2' : (2 : K[X]) ≠ 0 := by
    have hC := C_ne_zero.mpr h2
    rwa [map_ofNat] at hC
  have hd : derivative B₀ = 0 := by
    rcases mul_eq_zero.mp hE2 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' h2'
      · exact absurd h' hA
    · exact h
  have h11 : (derivative B₀).coeff 11 = 0 := by rw [hd]; simp
  rw [coeff_derivative] at h11
  have hnorm : ((11 : ℕ) : K) + 1 = 12 := by norm_num
  rw [hnorm] at h11
  rcases mul_eq_zero.mp h11 with h | h
  · exact hvertex h
  · exact h12 h

/-- In characteristic 3 the hypotheses of the §8.3 step are satisfiable:
    A₂ = X, B₀ = X¹² gives 2·A₂·B₀' = 2·X·12·X¹¹ = 0 while b₁₂ = 1 ≠ 0. -/
theorem t_zero_case_fails_char3 :
    ∃ A₂ B₀ : (ZMod 3)[X], A₂ ≠ 0 ∧ (2 : (ZMod 3)[X]) * A₂ * derivative B₀ = 0 ∧
      B₀.coeff 12 ≠ 0 := by
  refine ⟨X, X ^ 12, X_ne_zero, ?_, ?_⟩
  · rw [derivative_X_pow, show ((12 : ℕ) : ZMod 3) = 0 by decide]
    simp
  · simp

/-- Solvability of the seven affine conditions forces every 3×3 minor to vanish. -/
theorem minor_vanish {K : Type*} [CommRing K] {n : ℕ}
    (b M L : Fin n → K) (s₁ s₂ : K)
    (h : ∀ r, b r + s₁ * M r + s₂ * L r = 0) (i j k : Fin n) :
    Matrix.det !![b i, M i, L i; b j, M j, L j; b k, M k, L k] = 0 := by
  have hb : ∀ r, b r = -(s₁ * M r + s₂ * L r) := fun r => by
    linear_combination h r
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const]
  rw [hb i, hb j, hb k]
  ring

/-- The 3×3 minor polynomial det[b|M|L] on rows i, j, k. -/
noncomputable def minorPoly {K : Type*} [CommRing K] {n : ℕ}
    (b M L : Fin n → MvPolynomial (Fin 2) K) (i j k : Fin n) : MvPolynomial (Fin 2) K :=
  Matrix.det !![b i, M i, L i; b j, M j, L j; b k, M k, L k]

theorem eval_minorPoly {K : Type*} [CommRing K] {n : ℕ}
    (b M L : Fin n → MvPolynomial (Fin 2) K) (t : Fin 2 → K) (i j k : Fin n) :
    MvPolynomial.eval t (minorPoly b M L i j k) =
      Matrix.det !![MvPolynomial.eval t (b i), MvPolynomial.eval t (M i), MvPolynomial.eval t (L i);
                    MvPolynomial.eval t (b j), MvPolynomial.eval t (M j), MvPolynomial.eval t (L j);
                    MvPolynomial.eval t (b k), MvPolynomial.eval t (M k), MvPolynomial.eval t (L k)] := by
  unfold minorPoly
  rw [RingHom.map_det]
  congr 1
  ext r c
  fin_cases r <;> fin_cases c <;> rfl

/-- §8.4 logical skeleton: solvable E₂ conditions + span certificates for t₁⁵, t₂⁵ ⇒ t = 0. -/
theorem no_nonzero_direction {K : Type*} [Field K] {n : ℕ}
    (b M L : Fin n → MvPolynomial (Fin 2) K)
    (c₀ c₁ : Fin n × Fin n × Fin n → K)
    (hspan₀ : (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 5 =
      ∑ ijk, MvPolynomial.C (c₀ ijk) * minorPoly b M L ijk.1 ijk.2.1 ijk.2.2)
    (hspan₁ : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ 5 =
      ∑ ijk, MvPolynomial.C (c₁ ijk) * minorPoly b M L ijk.1 ijk.2.1 ijk.2.2)
    (t : Fin 2 → K) (s₁ s₂ : K)
    (hsolv : ∀ r, MvPolynomial.eval t (b r) + s₁ * MvPolynomial.eval t (M r)
      + s₂ * MvPolynomial.eval t (L r) = 0) :
    t = 0 := by
  have hz : ∀ ijk : Fin n × Fin n × Fin n,
      MvPolynomial.eval t (minorPoly b M L ijk.1 ijk.2.1 ijk.2.2) = 0 := by
    intro ijk
    rw [eval_minorPoly]
    exact minor_vanish _ _ _ s₁ s₂ hsolv _ _ _
  have key : ∀ (m : MvPolynomial (Fin 2) K) (c : Fin n × Fin n × Fin n → K),
      m = ∑ ijk, MvPolynomial.C (c ijk) * minorPoly b M L ijk.1 ijk.2.1 ijk.2.2 →
      MvPolynomial.eval t m = 0 := by
    intro m c hm
    rw [hm, map_sum]
    exact Finset.sum_eq_zero fun ijk _ => by rw [map_mul, hz ijk, mul_zero]
  have e0 := key _ c₀ hspan₀
  have e1 := key _ c₁ hspan₁
  simp only [map_pow, MvPolynomial.eval_X] at e0 e1
  funext i
  fin_cases i
  · simpa using pow_eq_zero_iff (n := 5) (by norm_num) |>.mp e0
  · simpa using pow_eq_zero_iff (n := 5) (by norm_num) |>.mp e1
