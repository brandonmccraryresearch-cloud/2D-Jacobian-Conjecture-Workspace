import Mathlib

/-!
# Branch (a), (b): the exact layer reduction

With `u = x y²`, write `P = Σₐ y^{-a} Aₐ(u)` (`a = 0, 1, 2`) and `Q = Σ_b y^{-b} B_b(u)`
(`b = 0, …, 3`).  Each piece `pₐ = y^{-a} Aₐ(u)` is a genuine polynomial, recorded by the
hypothesis `y^a · pₐ = Aₐ(x y²)`.

* `layer_bracket`: `y^{a+b+1} · J(p, q) = y² · (a A B' − b A' B)(x y²)`, from the derivation
  rules for `∂ₓ` and `∂ᵧ` only.
* `coeff_yev`: the coefficient of `xⁱ yⁿ` in `y^m · F(x y²)` is `F.coeff i` if `n = 2i + m`
  and `0` otherwise, so the layers `y^k · F_k(x y²)` have disjoint supports.
* `layers_of_jac`: `J(P, Q) = C λ · x²` forces the five layer identities E5, …, E1 in `K[u]`.
* `coeff_layerTerm`: `(a A B' − b A' B)ₙ = Σ_{i ≤ n+1} (a (n+1−i) − b i) Aᵢ B_{n+1−i}`, the scalar
  bracket equations (this is the monomial rule `[xⁱyʲ, xᵏyˡ] = (il − jk) x^{i+k−1} y^{j+l−1}`).
-/

open MvPolynomial

noncomputable section

namespace BranchAb

variable {K : Type*} [Field K]

/-- The Jacobian bracket `P_x Q_y − P_y Q_x`. -/
def jac (P Q : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  pderiv 0 P * pderiv 1 Q - pderiv 1 P * pderiv 0 Q

/-- `u = x y²`. -/
def uu : MvPolynomial (Fin 2) K := X 0 * X 1 ^ 2

/-- `A ↦ A(x y²)`. -/
def evH : Polynomial K →ₐ[K] MvPolynomial (Fin 2) K := Polynomial.aeval (uu (K := K))

/-- The layer term `a A B' − b A' B`. -/
def layerTerm (a b : ℕ) (A B : Polynomial K) : Polynomial K :=
  (a : Polynomial K) * A * Polynomial.derivative B - (b : Polynomial K) * Polynomial.derivative A * B

lemma jac_add_left (P P' Q : MvPolynomial (Fin 2) K) :
    jac (P + P') Q = jac P Q + jac P' Q := by
  simp only [jac, map_add]; ring

lemma jac_add_right (P Q Q' : MvPolynomial (Fin 2) K) :
    jac P (Q + Q') = jac P Q + jac P Q' := by
  simp only [jac, map_add]; ring

lemma pderiv0_uu : pderiv 0 (uu (K := K)) = X 1 ^ 2 := by
  simp [uu, pderiv_X]

lemma pderiv1_uu : pderiv 1 (uu (K := K)) = 2 * X 0 * X 1 := by
  simp [uu, pderiv_X, Derivation.leibniz_pow]; ring

lemma pderiv0_evH (A : Polynomial K) :
    pderiv 0 (evH A) = evH (Polynomial.derivative A) * X 1 ^ 2 := by
  show pderiv 0 (Polynomial.aeval uu A) = Polynomial.aeval uu (Polynomial.derivative A) * X 1 ^ 2
  rw [Derivation.map_aeval, pderiv0_uu, smul_eq_mul]

lemma pderiv1_evH (A : Polynomial K) :
    pderiv 1 (evH A) = evH (Polynomial.derivative A) * (2 * X 0 * X 1) := by
  show pderiv 1 (Polynomial.aeval uu A) = Polynomial.aeval uu (Polynomial.derivative A) * (2 * X 0 * X 1)
  rw [Derivation.map_aeval, pderiv1_uu, smul_eq_mul]

lemma X1_mul_pderiv1_X1_pow (a : ℕ) :
    (X 1 : MvPolynomial (Fin 2) K) * pderiv 1 (X 1 ^ a) = (a : MvPolynomial (Fin 2) K) * X 1 ^ a := by
  rcases a with _ | a
  · simp
  · rw [Derivation.leibniz_pow, pderiv_X_self, smul_eq_mul, nsmul_eq_mul, pow_succ]
    push_cast; ring

lemma pderiv0_X1_pow (a : ℕ) : pderiv 0 ((X 1 : MvPolynomial (Fin 2) K) ^ a) = 0 := by
  rw [Derivation.leibniz_pow, pderiv_X_of_ne (by decide)]; simp

/-- The per-layer bracket identity `y^{a+b+1} J(p, q) = y² (a A B' − b A' B)(x y²)`. -/
theorem layer_bracket (a b : ℕ) (A B : Polynomial K) (p q : MvPolynomial (Fin 2) K)
    (hp : X 1 ^ a * p = evH A) (hq : X 1 ^ b * q = evH B) :
    X 1 ^ (a + b + 1) * jac p q = X 1 ^ 2 * evH (layerTerm a b A B) := by
  have hx : ∀ (c : ℕ) (r : MvPolynomial (Fin 2) K) (C' : Polynomial K),
      X 1 ^ c * r = evH C' → X 1 ^ c * pderiv 0 r = evH (Polynomial.derivative C') * X 1 ^ 2 := by
    intro c r C' h
    have := congrArg (pderiv 0) h
    rw [Derivation.leibniz, pderiv0_X1_pow, smul_zero, add_zero, smul_eq_mul, pderiv0_evH] at this
    exact this
  have hy : ∀ (c : ℕ) (r : MvPolynomial (Fin 2) K) (C' : Polynomial K),
      X 1 ^ c * r = evH C' →
        X 1 ^ (c + 1) * pderiv 1 r =
          2 * uu * evH (Polynomial.derivative C') - (c : MvPolynomial (Fin 2) K) * evH C' := by
    intro c r C' h
    have h1 := congrArg (fun s => X 1 * pderiv 1 s) h
    simp only [Derivation.leibniz, smul_eq_mul, pderiv1_evH] at h1
    have e := X1_mul_pderiv1_X1_pow (K := K) c
    rw [← h, uu]
    linear_combination h1 - r * e
  have ha0 := hx a p A hp
  have hb0 := hx b q B hq
  have ha1 := hy a p A hp
  have hb1 := hy b q B hq
  have hev : evH (layerTerm a b A B) =
      (a : MvPolynomial (Fin 2) K) * (evH A * evH (Polynomial.derivative B)) -
        (b : MvPolynomial (Fin 2) K) * (evH (Polynomial.derivative A) * evH B) := by
    simp only [layerTerm, map_sub, map_mul, map_natCast]
    ring
  rw [hev, jac]
  linear_combination (X 1 ^ (b + 1) * pderiv 1 q) * ha0 +
    (evH (Polynomial.derivative A) * X 1 ^ 2) * hb1 -
    (X 1 ^ b * pderiv 0 q) * ha1 -
    (2 * uu * evH (Polynomial.derivative A) - (a : MvPolynomial (Fin 2) K) * evH A) * hb0

lemma X1_pow_mul_C_mul_uu_pow (m j : ℕ) (c : K) :
    (X 1 : MvPolynomial (Fin 2) K) ^ m * (C c * uu ^ j) =
      monomial (Finsupp.single 0 j + Finsupp.single 1 (2 * j + m)) c := by
  have hs : Finsupp.single (1 : Fin 2) m + (Finsupp.single 0 j + Finsupp.single 1 (2 * j)) =
      Finsupp.single 0 j + Finsupp.single 1 (2 * j + m) := by
    ext k; fin_cases k <;> simp; omega
  rw [uu, mul_pow, ← pow_mul, X_pow_eq_monomial, X_pow_eq_monomial, X_pow_eq_monomial,
    monomial_mul_monomial, C_mul_monomial, monomial_mul_monomial, hs]
  simp

/-- Coefficients of `y^m · F(x y²)`. -/
lemma coeff_yev (F : Polynomial K) (m i n : ℕ) :
    (X 1 ^ m * evH F).coeff (Finsupp.single 0 i + Finsupp.single 1 n) =
      if n = 2 * i + m then F.coeff i else 0 := by
  have hs : evH F = ∑ j ∈ Finset.range (F.natDegree + 1), C (F.coeff j) * uu ^ j := by
    show Polynomial.aeval uu F = _
    rw [Polynomial.aeval_eq_sum_range]
    simp only [smul_eq_C_mul]
  rw [hs, Finset.mul_sum]
  simp only [X1_pow_mul_C_mul_uu_pow, coeff_sum, coeff_monomial]
  have key : ∀ j : ℕ, (Finsupp.single (0 : Fin 2) j + Finsupp.single 1 (2 * j + m) =
      Finsupp.single 0 i + Finsupp.single 1 n) ↔ (j = i ∧ n = 2 * i + m) := by
    intro j
    constructor
    · intro h
      have h0 := congrArg (fun f => f 0) h
      have h1 := congrArg (fun f => f 1) h
      simp at h0 h1
      subst h0; exact ⟨rfl, h1.symm⟩
    · rintro ⟨rfl, rfl⟩; rfl
  simp only [key]
  by_cases hn : n = 2 * i + m
  · simp only [hn, and_true, ite_true]
    rw [Finset.sum_ite_eq' (Finset.range (F.natDegree + 1)) i (fun j => F.coeff j)]
    split_ifs with hi
    · rfl
    · simp only [Finset.mem_range, not_lt] at hi
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
  · simp [hn]

/-- If `Σ_{k<5} y^k · F_k(x y²) = 0` then every `F_k = 0`. -/
lemma layers_eq_zero (F : Fin 5 → Polynomial K)
    (h : ∑ k : Fin 5, X 1 ^ (k : ℕ) * evH (F k) = 0) (k : Fin 5) : F k = 0 := by
  ext i
  have := congrArg (fun p : MvPolynomial (Fin 2) K => p.coeff (Finsupp.single 0 i + Finsupp.single 1 (2 * i + k))) h
  simp only [coeff_sum] at this
  rw [show (0 : MvPolynomial (Fin 2) K).coeff _ = 0 from rfl] at this
  simp only [coeff_yev] at this
  rw [Finset.sum_eq_single k] at this
  · simpa using this
  · intro j _ hj
    have hkj : (k : ℕ) ≠ (j : ℕ) := fun e => hj (Fin.ext e.symm)
    simp [hkj]
  · simp

/-- **Exact layer reduction.**  `J(P, Q) = C λ x²` forces the five layer identities. -/
theorem layers_of_jac (lam : K) (A₀ A₁ A₂ B₀ B₁ B₂ B₃ : Polynomial K)
    (p₀ p₁ p₂ q₀ q₁ q₂ q₃ : MvPolynomial (Fin 2) K)
    (hp₀ : X 1 ^ 0 * p₀ = evH A₀) (hp₁ : X 1 ^ 1 * p₁ = evH A₁) (hp₂ : X 1 ^ 2 * p₂ = evH A₂)
    (hq₀ : X 1 ^ 0 * q₀ = evH B₀) (hq₁ : X 1 ^ 1 * q₁ = evH B₁) (hq₂ : X 1 ^ 2 * q₂ = evH B₂)
    (hq₃ : X 1 ^ 3 * q₃ = evH B₃)
    (hJ : jac (p₀ + p₁ + p₂) (q₀ + q₁ + q₂ + q₃) = C lam * X 0 ^ 2) :
    layerTerm 2 3 A₂ B₃ = Polynomial.C lam * Polynomial.X ^ 2 ∧
    layerTerm 2 2 A₂ B₂ + layerTerm 1 3 A₁ B₃ = 0 ∧
    layerTerm 2 1 A₂ B₁ + layerTerm 1 2 A₁ B₂ + layerTerm 0 3 A₀ B₃ = 0 ∧
    layerTerm 2 0 A₂ B₀ + layerTerm 1 1 A₁ B₁ + layerTerm 0 2 A₀ B₂ = 0 ∧
    layerTerm 1 0 A₁ B₀ + layerTerm 0 1 A₀ B₁ = 0 := by
  have e23 := layer_bracket 2 3 A₂ B₃ p₂ q₃ hp₂ hq₃
  have e22 := layer_bracket 2 2 A₂ B₂ p₂ q₂ hp₂ hq₂
  have e13 := layer_bracket 1 3 A₁ B₃ p₁ q₃ hp₁ hq₃
  have e21 := layer_bracket 2 1 A₂ B₁ p₂ q₁ hp₂ hq₁
  have e12 := layer_bracket 1 2 A₁ B₂ p₁ q₂ hp₁ hq₂
  have e03 := layer_bracket 0 3 A₀ B₃ p₀ q₃ hp₀ hq₃
  have e20 := layer_bracket 2 0 A₂ B₀ p₂ q₀ hp₂ hq₀
  have e11 := layer_bracket 1 1 A₁ B₁ p₁ q₁ hp₁ hq₁
  have e02 := layer_bracket 0 2 A₀ B₂ p₀ q₂ hp₀ hq₂
  have e10 := layer_bracket 1 0 A₁ B₀ p₁ q₀ hp₁ hq₀
  have e01 := layer_bracket 0 1 A₀ B₁ p₀ q₁ hp₀ hq₁
  have e00 := layer_bracket 0 0 A₀ B₀ p₀ q₀ hp₀ hq₀
  have hl00 : layerTerm 0 0 A₀ B₀ = 0 := by simp [layerTerm]
  rw [hl00, map_zero, mul_zero] at e00
  simp only [jac_add_left, jac_add_right] at hJ
  have hx2 : (X 1 : MvPolynomial (Fin 2) K) ^ 7 * (C lam * X 0 ^ 2) =
      X 1 ^ 3 * evH (Polynomial.C lam * Polynomial.X ^ 2) := by
    show _ = X 1 ^ 3 * Polynomial.aeval uu (Polynomial.C lam * Polynomial.X ^ 2)
    simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, uu, algebraMap_eq]
    ring
  set F : Fin 5 → Polynomial K := ![
    layerTerm 2 3 A₂ B₃ - Polynomial.C lam * Polynomial.X ^ 2,
    layerTerm 2 2 A₂ B₂ + layerTerm 1 3 A₁ B₃,
    layerTerm 2 1 A₂ B₁ + layerTerm 1 2 A₁ B₂ + layerTerm 0 3 A₀ B₃,
    layerTerm 2 0 A₂ B₀ + layerTerm 1 1 A₁ B₁ + layerTerm 0 2 A₀ B₂,
    layerTerm 1 0 A₁ B₀ + layerTerm 0 1 A₀ B₁] with hF
  have hsum : X 1 ^ 3 * ∑ k : Fin 5, X 1 ^ (k : ℕ) * evH (F k) = 0 := by
    simp only [Fin.sum_univ_five, hF, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, map_add, map_sub, Fin.val_zero, Fin.val_one, Fin.val_two]
    have h7 := congrArg (fun s => X 1 ^ 7 * s) hJ
    rw [hx2] at h7
    have v3 : ((3 : Fin 5) : ℕ) = 3 := rfl
    have v4 : ((4 : Fin 5) : ℕ) = 4 := rfl
    rw [v3, v4]
    linear_combination h7 - X 1 ^ 1 * e23 - X 1 ^ 2 * e22 - X 1 ^ 2 * e13 -
      X 1 ^ 3 * e21 - X 1 ^ 3 * e12 - X 1 ^ 3 * e03 - X 1 ^ 4 * e20 - X 1 ^ 4 * e11 -
      X 1 ^ 4 * e02 - X 1 ^ 5 * e10 - X 1 ^ 5 * e01 - X 1 ^ 6 * e00
  have hs : ∑ k : Fin 5, X 1 ^ (k : ℕ) * evH (F k) = 0 := by
    rcases mul_eq_zero.mp hsum with h | h
    · exact absurd h (pow_ne_zero _ (X_ne_zero 1))
    · exact h
  have z := layers_eq_zero F hs
  refine ⟨?_, z 1, z 2, z 3, z 4⟩
  have := z 0
  simp only [hF, Matrix.cons_val_zero] at this
  exact sub_eq_zero.mp this

/-- Coefficients of a layer term: `(a A B' − b A' B)ₙ = Σ_{i ≤ n+1} (a (n+1−i) − b i) Aᵢ B_{n+1−i}`. -/
theorem coeff_layerTerm (a b n : ℕ) (A B : Polynomial K) :
    (layerTerm a b A B).coeff n =
      ∑ i ∈ Finset.range (n + 2),
        ((a : K) * ((n + 1 - i : ℕ) : K) - (b : K) * (i : K)) * A.coeff i * B.coeff (n + 1 - i) := by
  have h1 : ((a : Polynomial K) * A * Polynomial.derivative B).coeff n =
      ∑ i ∈ Finset.range (n + 2), (a : K) * ((n + 1 - i : ℕ) : K) * A.coeff i * B.coeff (n + 1 - i) := by
    rw [mul_assoc, Polynomial.coeff_natCast_mul, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ _ (n + 1), Finset.mul_sum]
    simp only [Polynomial.coeff_derivative, Nat.sub_self, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e1 : n - i + 1 = n + 1 - i := by omega
    rw [e1]; push_cast [Nat.cast_sub hi', Nat.cast_sub (by omega : i ≤ n + 1)]; ring
  have h2 : ((b : Polynomial K) * Polynomial.derivative A * B).coeff n =
      ∑ i ∈ Finset.range (n + 2), (b : K) * (i : K) * A.coeff i * B.coeff (n + 1 - i) := by
    rw [mul_assoc, Polynomial.coeff_natCast_mul, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ' _ (n + 1), Finset.mul_sum]
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp only [Polynomial.coeff_derivative]
    have e1 : n + 1 - (i + 1) = n - i := by omega
    rw [e1]; push_cast; ring
  rw [layerTerm, Polynomial.coeff_sub, h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => by ring)

end BranchAb
