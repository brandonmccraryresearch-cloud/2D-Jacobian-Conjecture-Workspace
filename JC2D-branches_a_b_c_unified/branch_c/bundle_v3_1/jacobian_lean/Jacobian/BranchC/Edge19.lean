import Jacobian.BranchC.LayerE2

/-!
# Branch (c): the `x¹⁹` edge identity and vertex–edge rigidity

Grade `K[x,y]` by the degree in `x` (`w(x) = 1`, `w(y) = 0`). The bracket `J(p,q) = p_x q_y − p_y q_x`
maps degrees `(a, b)` to `a + b − 1`. If `P` has `x`-degree `≤ 8` and `Q` has `x`-degree `≤ 12`, the
`x¹⁹` part of `J(P,Q)` is `J(x⁸ f(y), x¹² g(y)) = x¹⁹ (8 f g′ − 12 f′ g)`, where `f = [x⁸]P` and
`g = [x¹²]Q` (`colPoly`). So `J(P,Q) = λx²` forces `8 f g′ = 12 f′ g` (`x19_identity_of_jac`).

For the branch-(c) polygons the two columns are the vertical edges
`f = α y¹⁴ + a₁ y¹⁵ + a₀ y¹⁶` (`α = a_{8,14}`) and `g = β y²¹ + t y²² + s y²³ + b y²⁴` (`β = b_{12,21}`),
and the `y³⁵ … y³⁸` coefficients of `2 f g′ − 3 f′ g` are (`edge_coeffs`)

  `2αt − 3βa₁ = 0`,  `4αs − a₁t − 6βa₀ = 0`,  `6αb + a₁s − 4a₀t = 0`,  `3a₁b − 2a₀s = 0`.

These are the `u¹⁹` coefficients of the `E₄, E₃, E₂, E₁` layer identities (`E₄`: `h4_19_35`, `E₃`:
`h3_19_36`, `E₂`: `h2_19_37`, `E₁`: the bracket monomial `x¹⁹y³⁸`). With `αβ ≠ 0` (`edge19_rigidity`):

  `3β s = t²`,  `27β² b = t³`,  `3β a₁ = 2α t`,  `9β² a₀ = α t²`,

i.e. `f = α(1 + γy)² y¹⁴`, `g = β(1 + γy)³ y²¹` with `γ = t/(3β)`. In the descent coordinates
`t₂ = b_{12,22}`, `s₂ = b_{12,23}` this is the `E₁` obstruction `Ω(t₂, s₂) = 0` (whose double root is
`κ = 1/(3 b_{12,21})`, see `Jacobian/BranchC/OmegaEdge.lean`), and it also gives
`b_{12,24} = t₂³/(27 b_{12,21}²)`: the vertex `(12,24)` forces `t₂ ≠ 0` (`vertex_12_24_forces_t2`), which
contains the Degree-19 lemma (`t = 0 ⇒ b_{12,24} = 0`) as the special case `t₂ = 0`.

No `sorry`, no new axioms.
-/

open MvPolynomial

noncomputable section

namespace BranchC

open BranchAb

variable {K : Type*} [Field K]

/-! ### The `x`-degree grading -/

/-- `w(x) = 1`, `w(y) = 0`. -/
def xw : Fin 2 → ℤ := ![1, 0]

lemma weight_xw (d : Fin 2 →₀ ℕ) : Finsupp.weight xw d = (d 0 : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]
  simp [Fin.sum_univ_two, xw]

lemma isWHx_pderiv {p : MvPolynomial (Fin 2) K} {a : ℤ} (hp : IsWeightedHomogeneous xw p a)
    (i : Fin 2) : IsWeightedHomogeneous xw (pderiv i p) (a - xw i) := by
  intro d hd
  rw [coeff_pderiv] at hd
  have h := hp (left_ne_zero_of_mul hd)
  rw [map_add, Finsupp.weight_single, one_smul] at h
  linarith

/-- The bracket maps `x`-degrees `(a, b)` to `a + b − 1`. -/
lemma isWHx_jac {p q : MvPolynomial (Fin 2) K} {a b : ℤ}
    (hp : IsWeightedHomogeneous xw p a) (hq : IsWeightedHomogeneous xw q b) :
    IsWeightedHomogeneous xw (jac p q) (a + b - 1) := by
  have h01 := (isWHx_pderiv hp 0).mul (isWHx_pderiv hq 1)
  have h10 := (isWHx_pderiv hp 1).mul (isWHx_pderiv hq 0)
  have x0 : xw 0 = 1 := rfl
  have x1 : xw 1 = 0 := rfl
  have e1 : a - xw 0 + (b - xw 1) = a + b - 1 := by rw [x0, x1]; ring
  have e2 : a - xw 1 + (b - xw 0) = a + b - 1 := by rw [x0, x1]; ring
  rw [e1] at h01
  rw [e2] at h10
  exact h01.sub h10

/-- The `x`-degree-`k` component. -/
abbrev xcomp (k : ℤ) (F : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  weightedHomogeneousComponent xw k F

lemma coeff_xcomp (k : ℤ) (F : MvPolynomial (Fin 2) K) (d : Fin 2 →₀ ℕ) :
    (xcomp k F).coeff d = if (d 0 : ℤ) = k then F.coeff d else 0 := by
  rw [coeff_weightedHomogeneousComponent, weight_xw]

lemma isWHx_xcomp (k : ℤ) (F : MvPolynomial (Fin 2) K) : IsWeightedHomogeneous xw (xcomp k F) k :=
  weightedHomogeneousComponent_isWeightedHomogeneous k F

/-- A polynomial whose `x`-degrees lie in `s` is the sum of its components over `s`. -/
lemma eq_sum_xcomp (F : MvPolynomial (Fin 2) K) (s : Finset ℤ)
    (hs : ∀ d ∈ F.support, (d 0 : ℤ) ∈ s) : F = ∑ k ∈ s, xcomp k F := by
  ext d
  rw [coeff_sum]
  simp only [coeff_xcomp]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hs d (mem_support_iff.mpr hne))

/-! ### Columns: the coefficient of `xⁱ` as a polynomial in `y` -/

/-- `[xⁱ]P ∈ K[y]`. -/
def colPoly (P : MvPolynomial (Fin 2) K) (i : ℕ) : Polynomial K :=
  ∑ m ∈ P.support.filter (fun m => m 0 = i), Polynomial.monomial (m 1) (P.coeff m)

theorem coeff_colPoly (P : MvPolynomial (Fin 2) K) (i j : ℕ) :
    (colPoly P i).coeff j = P.coeff (mono i j) := by
  unfold colPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_filter]
  have key : ∀ m : Fin 2 →₀ ℕ, (m 0 = i ∧ m 1 = j) ↔ m = mono i j := by
    intro m
    constructor
    · rintro ⟨h0, h1⟩
      ext k; fin_cases k <;> simp [h0, h1]
    · rintro rfl; simp
  simp only [← ite_and, key]
  rw [Finset.sum_ite_eq']
  split_ifs with hs
  · rfl
  · exact (notMem_support_iff.mp hs).symm

/-- `F ↦ F(y)`. -/
def yv : Polynomial K →ₐ[K] MvPolynomial (Fin 2) K := Polynomial.aeval (X 1)

private lemma X0_pow_mul_C_mul_X1_pow (i j : ℕ) (c : K) :
    (X 0 ^ i * (C c * X 1 ^ j) : MvPolynomial (Fin 2) K) = monomial (mono i j) c := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, C_mul_monomial, monomial_mul_monomial, mul_one, one_mul]

/-- Coefficients of `xⁱ · F(y)`. -/
lemma coeff_X0_pow_mul_yv (F : Polynomial K) (i a b : ℕ) :
    (X 0 ^ i * yv F).coeff (mono a b) = if a = i then F.coeff b else 0 := by
  have hs : yv F = ∑ j ∈ Finset.range (F.natDegree + 1), C (F.coeff j) * X 1 ^ j := by
    show Polynomial.aeval (X 1) F = _
    rw [Polynomial.aeval_eq_sum_range]
    simp only [smul_eq_C_mul]
  rw [hs, Finset.mul_sum]
  simp only [X0_pow_mul_C_mul_X1_pow, coeff_sum, coeff_monomial]
  have key : ∀ j : ℕ, (mono i j = mono a b) ↔ (j = b ∧ a = i) := by
    intro j
    constructor
    · intro h
      have h0 := congrArg (fun f => f 0) h
      have h1 := congrArg (fun f => f 1) h
      simp at h0 h1
      exact ⟨h1, h0.symm⟩
    · rintro ⟨rfl, rfl⟩; rfl
  simp only [key]
  by_cases ha : a = i
  · simp only [ha, and_true, ite_true]
    rw [Finset.sum_ite_eq' (Finset.range (F.natDegree + 1)) b (fun j => F.coeff j)]
    split_ifs with hb
    · rfl
    · simp only [Finset.mem_range, not_lt] at hb
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
  · simp [ha]

/-- `F(y) = 0` forces `F = 0`. -/
lemma yv_eq_zero {F : Polynomial K} (h : yv F = 0) : F = 0 := by
  ext b
  have := coeff_X0_pow_mul_yv F 0 0 b
  rw [pow_zero, one_mul, h] at this
  simpa using this.symm

/-- The `x`-degree-`i` component is `xⁱ · ([xⁱ]P)(y)`. -/
lemma xcomp_eq (P : MvPolynomial (Fin 2) K) (i : ℕ) :
    xcomp (i : ℤ) P = X 0 ^ i * yv (colPoly P i) := by
  ext d
  have hd : d = mono (d 0) (d 1) := (mono_eta d).symm
  rw [coeff_xcomp]
  conv_rhs => rw [hd]
  rw [coeff_X0_pow_mul_yv, coeff_colPoly]
  split_ifs with h1 h2 h2
  · rw [← h2, mono_eta]
  · exfalso; omega
  · exfalso; omega
  · rfl

/-! ### The bracket of two columns -/

lemma pderiv0_yv (F : Polynomial K) : pderiv 0 (yv F) = 0 := by
  show pderiv 0 (Polynomial.aeval (X 1) F) = 0
  rw [Derivation.map_aeval, pderiv_X_of_ne (by decide), smul_zero]

lemma pderiv1_yv (F : Polynomial K) : pderiv 1 (yv F) = yv (Polynomial.derivative F) := by
  show pderiv 1 (Polynomial.aeval (X 1) F) = Polynomial.aeval (X 1) (Polynomial.derivative F)
  rw [Derivation.map_aeval, pderiv_X_self, smul_eq_mul, mul_one]

lemma X0_mul_pderiv0_X0_pow (a : ℕ) :
    (X 0 : MvPolynomial (Fin 2) K) * pderiv 0 (X 0 ^ a) = (a : MvPolynomial (Fin 2) K) * X 0 ^ a := by
  rcases a with _ | a
  · simp
  · rw [Derivation.leibniz_pow, pderiv_X_self, smul_eq_mul, nsmul_eq_mul, pow_succ]
    push_cast; ring

lemma pderiv1_X0_pow (a : ℕ) : pderiv 1 ((X 0 : MvPolynomial (Fin 2) K) ^ a) = 0 := by
  rw [Derivation.leibniz_pow, pderiv_X_of_ne (by decide)]; simp

/-- `x · J(xⁱ f(y), xᵏ g(y)) = x^{i+k} · (i f g′ − k f′ g)(y)`. -/
theorem x_bracket (i k : ℕ) (f g : Polynomial K) :
    X 0 * jac (X 0 ^ i * yv f) (X 0 ^ k * yv g) =
      X 0 ^ (i + k) * yv ((i : Polynomial K) * f * Polynomial.derivative g -
        (k : Polynomial K) * Polynomial.derivative f * g) := by
  have hp0 : X 0 * pderiv 0 (X 0 ^ i * yv f) = (i : MvPolynomial (Fin 2) K) * (X 0 ^ i * yv f) := by
    rw [Derivation.leibniz, pderiv0_yv, smul_zero, zero_add, smul_eq_mul]
    linear_combination yv f * X0_mul_pderiv0_X0_pow (K := K) i
  have hq0 : X 0 * pderiv 0 (X 0 ^ k * yv g) = (k : MvPolynomial (Fin 2) K) * (X 0 ^ k * yv g) := by
    rw [Derivation.leibniz, pderiv0_yv, smul_zero, zero_add, smul_eq_mul]
    linear_combination yv g * X0_mul_pderiv0_X0_pow (K := K) k
  have hp1 : pderiv 1 (X 0 ^ i * yv f) = X 0 ^ i * yv (Polynomial.derivative f) := by
    rw [Derivation.leibniz, pderiv1_yv, pderiv1_X0_pow, smul_zero, add_zero, smul_eq_mul]
  have hq1 : pderiv 1 (X 0 ^ k * yv g) = X 0 ^ k * yv (Polynomial.derivative g) := by
    rw [Derivation.leibniz, pderiv1_yv, pderiv1_X0_pow, smul_zero, add_zero, smul_eq_mul]
  have hev : yv ((i : Polynomial K) * f * Polynomial.derivative g -
      (k : Polynomial K) * Polynomial.derivative f * g) =
      (i : MvPolynomial (Fin 2) K) * yv f * yv (Polynomial.derivative g) -
        (k : MvPolynomial (Fin 2) K) * yv (Polynomial.derivative f) * yv g := by
    simp only [map_sub, map_mul, map_natCast]
  rw [hev, jac]
  linear_combination (pderiv 1 (X 0 ^ k * yv g)) * hp0 - (pderiv 1 (X 0 ^ i * yv f)) * hq0 +
    ((i : MvPolynomial (Fin 2) K) * (X 0 ^ i * yv f)) * hq1 -
    ((k : MvPolynomial (Fin 2) K) * (X 0 ^ k * yv g)) * hp1

/-! ### The `x¹⁹` identity -/

/-- **The `x¹⁹` edge identity.** If `P` has `x`-degree `≤ 8`, `Q` has `x`-degree `≤ 12` and
`J(P,Q) = λx²`, then `8 f g′ − 12 f′ g = 0` for `f = [x⁸]P`, `g = [x¹²]Q`. -/
theorem x19_identity_of_jac (lam : K) (P Q : MvPolynomial (Fin 2) K)
    (hP : ∀ m ∈ P.support, m 0 ≤ 8) (hQ : ∀ m ∈ Q.support, m 0 ≤ 12)
    (hJ : jac P Q = C lam * X 0 ^ 2) :
    (8 : Polynomial K) * colPoly P 8 * Polynomial.derivative (colPoly Q 12) -
      12 * Polynomial.derivative (colPoly P 8) * colPoly Q 12 = 0 := by
  classical
  have hPs : ∀ d ∈ P.support, (d 0 : ℤ) ∈ Finset.Icc (0 : ℤ) 8 := by
    intro d hd; have := hP d hd; simp only [Finset.mem_Icc]; omega
  have hQs : ∀ d ∈ Q.support, (d 0 : ℤ) ∈ Finset.Icc (0 : ℤ) 12 := by
    intro d hd; have := hQ d hd; simp only [Finset.mem_Icc]; omega
  -- the `x¹⁹` component of `J(P,Q)`
  have hsplit : xcomp 19 (jac P Q) =
      ∑ k ∈ Finset.Icc (0 : ℤ) 8, ∑ l ∈ Finset.Icc (0 : ℤ) 12,
        if k + l - 1 = 19 then jac (xcomp k P) (xcomp l Q) else 0 := by
    conv_lhs => rw [eq_sum_xcomp P _ hPs, eq_sum_xcomp Q _ hQs, jac_sum_sum]
    simp only [map_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    have hkl := isWHx_jac (isWHx_xcomp k P) (isWHx_xcomp l Q)
    split_ifs with h
    · rw [← h]; exact hkl.weightedHomogeneousComponent_same
    · exact hkl.weightedHomogeneousComponent_ne 19 (Ne.symm h)
  have hpair : xcomp 19 (jac P Q) = jac (xcomp 8 P) (xcomp 12 Q) := by
    rw [hsplit]
    have e : ∀ k : ℤ, (∑ l ∈ Finset.Icc (0 : ℤ) 12,
        if k + l - 1 = 19 then jac (xcomp k P) (xcomp l Q) else 0) =
          if 20 - k ∈ Finset.Icc (0 : ℤ) 12 then jac (xcomp k P) (xcomp (20 - k) Q) else 0 := by
      intro k
      rw [← Finset.sum_ite_eq (Finset.Icc (0 : ℤ) 12) (20 - k) (fun l => jac (xcomp k P) (xcomp l Q))]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)
    simp only [e]
    rw [← Finset.sum_filter]
    have hf : (Finset.Icc (0 : ℤ) 8).filter (fun k => 20 - k ∈ Finset.Icc (0 : ℤ) 12) = {8} := by
      decide
    rw [hf, Finset.sum_singleton]
    norm_num
  -- the `x¹⁹` component of `λx²` vanishes
  have htgt : xcomp 19 (C lam * X 0 ^ 2 : MvPolynomial (Fin 2) K) = 0 := by
    have h2 : IsWeightedHomogeneous xw (C lam * X 0 ^ 2 : MvPolynomial (Fin 2) K) (0 + 2 • xw 0) :=
      (isWeightedHomogeneous_C xw lam).mul ((isWeightedHomogeneous_X K xw 0).pow 2)
    exact h2.weightedHomogeneousComponent_ne 19 (by simp [xw])
  have h0 : jac (X 0 ^ 8 * yv (colPoly P 8)) (X 0 ^ 12 * yv (colPoly Q 12)) = 0 := by
    have e8 : xcomp (8 : ℤ) P = X 0 ^ 8 * yv (colPoly P 8) := by exact_mod_cast xcomp_eq P 8
    have e12 : xcomp (12 : ℤ) Q = X 0 ^ 12 * yv (colPoly Q 12) := by exact_mod_cast xcomp_eq Q 12
    rw [← e8, ← e12, ← hpair, hJ, htgt]
  have hx := x_bracket 8 12 (colPoly P 8) (colPoly Q 12)
  rw [h0, mul_zero] at hx
  have hne : (X 0 : MvPolynomial (Fin 2) K) ^ (8 + 12) ≠ 0 := pow_ne_zero _ (X_ne_zero 0)
  have hy := yv_eq_zero ((mul_eq_zero.mp hx.symm).resolve_left hne)
  simpa using hy

/-! ### The edge equations -/

/-- The `y³⁵ … y³⁸` coefficients of `8 f g′ − 12 f′ g` for
`f = α y¹⁴ + a₁ y¹⁵ + a₀ y¹⁶`, `g = β y²¹ + t y²² + s y²³ + b y²⁴` (the `y³⁴` and `y³⁹` coefficients
vanish identically). -/
theorem edge_coeffs [CharZero K] (α a₁ a₀ β t s b : K)
    (hE : (8 : Polynomial K) *
        (Polynomial.C α * Polynomial.X ^ 14 + Polynomial.C a₁ * Polynomial.X ^ 15 +
          Polynomial.C a₀ * Polynomial.X ^ 16) *
        Polynomial.derivative (Polynomial.C β * Polynomial.X ^ 21 + Polynomial.C t * Polynomial.X ^ 22 +
          Polynomial.C s * Polynomial.X ^ 23 + Polynomial.C b * Polynomial.X ^ 24) -
      12 * Polynomial.derivative (Polynomial.C α * Polynomial.X ^ 14 +
          Polynomial.C a₁ * Polynomial.X ^ 15 + Polynomial.C a₀ * Polynomial.X ^ 16) *
        (Polynomial.C β * Polynomial.X ^ 21 + Polynomial.C t * Polynomial.X ^ 22 +
          Polynomial.C s * Polynomial.X ^ 23 + Polynomial.C b * Polynomial.X ^ 24) = 0) :
    2 * α * t - 3 * β * a₁ = 0 ∧ 4 * α * s - a₁ * t - 6 * β * a₀ = 0 ∧
      6 * α * b + a₁ * s - 4 * a₀ * t = 0 ∧ 3 * a₁ * b - 2 * a₀ * s = 0 := by
  have key : (8 : Polynomial K) *
        (Polynomial.C α * Polynomial.X ^ 14 + Polynomial.C a₁ * Polynomial.X ^ 15 +
          Polynomial.C a₀ * Polynomial.X ^ 16) *
        Polynomial.derivative (Polynomial.C β * Polynomial.X ^ 21 + Polynomial.C t * Polynomial.X ^ 22 +
          Polynomial.C s * Polynomial.X ^ 23 + Polynomial.C b * Polynomial.X ^ 24) -
      12 * Polynomial.derivative (Polynomial.C α * Polynomial.X ^ 14 +
          Polynomial.C a₁ * Polynomial.X ^ 15 + Polynomial.C a₀ * Polynomial.X ^ 16) *
        (Polynomial.C β * Polynomial.X ^ 21 + Polynomial.C t * Polynomial.X ^ 22 +
          Polynomial.C s * Polynomial.X ^ 23 + Polynomial.C b * Polynomial.X ^ 24) =
      Polynomial.C (4 * (2 * α * t - 3 * β * a₁)) * Polynomial.X ^ 35 +
        Polynomial.C (4 * (4 * α * s - a₁ * t - 6 * β * a₀)) * Polynomial.X ^ 36 +
        Polynomial.C (4 * (6 * α * b + a₁ * s - 4 * a₀ * t)) * Polynomial.X ^ 37 +
        Polynomial.C (4 * (3 * a₁ * b - 2 * a₀ * s)) * Polynomial.X ^ 38 := by
    simp only [Polynomial.derivative_C_mul_X_pow, map_mul, map_sub, map_add, map_ofNat, Nat.cast_ofNat]
    ring
  rw [key] at hE
  have c : ∀ n : ℕ, (Polynomial.C (4 * (2 * α * t - 3 * β * a₁)) * Polynomial.X ^ 35 +
        Polynomial.C (4 * (4 * α * s - a₁ * t - 6 * β * a₀)) * Polynomial.X ^ 36 +
        Polynomial.C (4 * (6 * α * b + a₁ * s - 4 * a₀ * t)) * Polynomial.X ^ 37 +
        Polynomial.C (4 * (3 * a₁ * b - 2 * a₀ * s)) * Polynomial.X ^ 38 : Polynomial K).coeff n = 0 :=
    fun n => by rw [hE, Polynomial.coeff_zero]
  have c35 := c 35
  have c36 := c 36
  have c37 := c 37
  have c38 := c 38
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow] at c35 c36 c37 c38
  norm_num at c35 c36 c37 c38
  exact ⟨c35, c36, c37, c38⟩

/-- **Vertex–edge rigidity.** The four edge equations with `α ≠ 0` force
`3βs = t²`, `27β²b = t³`, `3βa₁ = 2αt`, `9β²a₀ = αt²`. (Cofactors from Singular `lift`; `β ≠ 0` is
not needed.) -/
theorem edge19_rigidity [CharZero K] (α a₁ a₀ β t s b : K) (hα : α ≠ 0)
    (h35 : 2 * α * t - 3 * β * a₁ = 0) (h36 : 4 * α * s - a₁ * t - 6 * β * a₀ = 0)
    (h37 : 6 * α * b + a₁ * s - 4 * a₀ * t = 0) (h38 : 3 * a₁ * b - 2 * a₀ * s = 0) :
    3 * β * s = t ^ 2 ∧ 27 * β ^ 2 * b = t ^ 3 ∧ 3 * β * a₁ = 2 * α * t ∧
      9 * β ^ 2 * a₀ = α * t ^ 2 := by
  have hsq : α * (3 * β * s - t ^ 2) ^ 2 = 0 := by
    linear_combination (t ^ 3 / 2 - 27 * b * β ^ 2 / 4) * h35 +
      (-3 * t ^ 2 * β / 2 + 9 * s * β ^ 2 / 4) * h36 + (9 * t * β ^ 2 / 4) * h37 +
      (-27 * β ^ 3 / 4) * h38
  have hs : 3 * β * s = t ^ 2 :=
    sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp hsq).resolve_left hα))
  have hb' : α * (27 * β ^ 2 * b - 9 * β * s * t + 2 * t ^ 3) = 0 := by
    linear_combination (t ^ 2 + 3 * s * β / 2) * h35 + (-3 * t * β) * h36 + (9 * β ^ 2 / 2) * h37
  have hb'' := (mul_eq_zero.mp hb').resolve_left hα
  refine ⟨hs, ?_, ?_, ?_⟩
  · linear_combination hb'' + 3 * t * hs
  · linear_combination -h35
  · linear_combination (t / 2) * h35 - (3 * β / 2) * h36 + 2 * α * hs

/-- Without the `y³⁸` equation: `t = 0` already forces `b = 0` (the Degree-19 mechanism). -/
theorem edge19_t_zero [CharZero K] (α a₁ a₀ β t s b : K) (hα : α ≠ 0) (hβ : β ≠ 0)
    (h35 : 2 * α * t - 3 * β * a₁ = 0) (h36 : 4 * α * s - a₁ * t - 6 * β * a₀ = 0)
    (h37 : 6 * α * b + a₁ * s - 4 * a₀ * t = 0) (ht : t = 0) : b = 0 := by
  have hb' : α * (27 * β ^ 2 * b - 9 * β * s * t + 2 * t ^ 3) = 0 := by
    linear_combination (t ^ 2 + 3 * s * β / 2) * h35 + (-3 * t * β) * h36 + (9 * β ^ 2 / 2) * h37
  subst ht
  have h := (mul_eq_zero.mp hb').resolve_left hα
  have h27 : (27 : K) * β ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hβ)
  have : (27 * β ^ 2) * b = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left h27

/-! ### For `P, Q` with the branch-(c) polygons -/

/-- The `x⁸` column of `P`: the vertical edge `(8,14)–(8,16)`. -/
lemma colPoly_P8 (P : MvPolynomial (Fin 2) K) (hP : ∀ m ∈ P.support, inNPc m) :
    colPoly P 8 = Polynomial.C (P.coeff (mono 8 14)) * Polynomial.X ^ 14 +
      Polynomial.C (P.coeff (mono 8 15)) * Polynomial.X ^ 15 +
      Polynomial.C (P.coeff (mono 8 16)) * Polynomial.X ^ 16 := by
  ext j
  rw [coeff_colPoly]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  by_cases h14 : j = 14
  · subst h14; simp
  by_cases h15 : j = 15
  · subst h15; simp
  by_cases h16 : j = 16
  · subst h16; simp
  simp only [h14, h15, h16, ite_false, add_zero]
  exact notMem_support_iff.mp (fun h => by have := hP _ h; simp [inNPc] at this; omega)

/-- The `x¹²` column of `Q`: the vertical edge `(12,21)–(12,24)`. -/
lemma colPoly_Q12 (Q : MvPolynomial (Fin 2) K) (hQ : ∀ m ∈ Q.support, inNQc m) :
    colPoly Q 12 = Polynomial.C (Q.coeff (mono 12 21)) * Polynomial.X ^ 21 +
      Polynomial.C (Q.coeff (mono 12 22)) * Polynomial.X ^ 22 +
      Polynomial.C (Q.coeff (mono 12 23)) * Polynomial.X ^ 23 +
      Polynomial.C (Q.coeff (mono 12 24)) * Polynomial.X ^ 24 := by
  ext j
  rw [coeff_colPoly]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  by_cases h21 : j = 21
  · subst h21; simp
  by_cases h22 : j = 22
  · subst h22; simp
  by_cases h23 : j = 23
  · subst h23; simp
  by_cases h24 : j = 24
  · subst h24; simp
  simp only [h21, h22, h23, h24, ite_false, add_zero]
  exact notMem_support_iff.mp (fun h => by have := hQ _ h; simp [inNQc] at this; omega)

/-- **The four edge equations for branch (c)**, from `J(P,Q) = λx²`. -/
theorem edge19_eqs_of_jac [CharZero K] (lam : K) (P Q : MvPolynomial (Fin 2) K)
    (hP : ∀ m ∈ P.support, inNPc m) (hQ : ∀ m ∈ Q.support, inNQc m)
    (hJ : jac P Q = C lam * X 0 ^ 2) :
    2 * P.coeff (mono 8 14) * Q.coeff (mono 12 22) - 3 * Q.coeff (mono 12 21) * P.coeff (mono 8 15) = 0 ∧
    4 * P.coeff (mono 8 14) * Q.coeff (mono 12 23) - P.coeff (mono 8 15) * Q.coeff (mono 12 22) -
      6 * Q.coeff (mono 12 21) * P.coeff (mono 8 16) = 0 ∧
    6 * P.coeff (mono 8 14) * Q.coeff (mono 12 24) + P.coeff (mono 8 15) * Q.coeff (mono 12 23) -
      4 * P.coeff (mono 8 16) * Q.coeff (mono 12 22) = 0 ∧
    3 * P.coeff (mono 8 15) * Q.coeff (mono 12 24) - 2 * P.coeff (mono 8 16) * Q.coeff (mono 12 23) = 0 := by
  have h := x19_identity_of_jac lam P Q (fun m hm => (hP m hm).1) (fun m hm => (hQ m hm).1) hJ
  rw [colPoly_P8 P hP, colPoly_Q12 Q hQ] at h
  exact edge_coeffs _ _ _ _ _ _ _ h

/-- **Vertex–edge rigidity for branch (c).** If `J(P,Q) = λx²`, `P, Q` are supported in the
branch-(c) polygons and `a_{8,14} ≠ 0` (a vertex), then with `t₂ = b_{12,22}`,
`s₂ = b_{12,23}`, `β = b_{12,21}`: `3β s₂ = t₂²` (the `E₁` obstruction `Ω = 0`) and
`27β² b_{12,24} = t₂³`. -/
theorem edge19_rigidity_of_jac [CharZero K] (lam : K) (P Q : MvPolynomial (Fin 2) K)
    (hP : ∀ m ∈ P.support, inNPc m) (hQ : ∀ m ∈ Q.support, inNQc m)
    (hJ : jac P Q = C lam * X 0 ^ 2) (hα : P.coeff (mono 8 14) ≠ 0) :
    3 * Q.coeff (mono 12 21) * Q.coeff (mono 12 23) = Q.coeff (mono 12 22) ^ 2 ∧
    27 * Q.coeff (mono 12 21) ^ 2 * Q.coeff (mono 12 24) = Q.coeff (mono 12 22) ^ 3 ∧
    3 * Q.coeff (mono 12 21) * P.coeff (mono 8 15) = 2 * P.coeff (mono 8 14) * Q.coeff (mono 12 22) ∧
    9 * Q.coeff (mono 12 21) ^ 2 * P.coeff (mono 8 16) = P.coeff (mono 8 14) * Q.coeff (mono 12 22) ^ 2 := by
  obtain ⟨h35, h36, h37, h38⟩ := edge19_eqs_of_jac lam P Q hP hQ hJ
  exact edge19_rigidity _ _ _ _ _ _ _ hα h35 h36 h37 h38

/-- **The vertex `(12,24)` forces `t₂ ≠ 0`.** (Contains the Degree-19 lemma: `t₂ = 0 ⇒ b_{12,24} = 0`.) -/
theorem vertex_12_24_forces_t2 [CharZero K] (lam : K) (P Q : MvPolynomial (Fin 2) K)
    (hP : ∀ m ∈ P.support, inNPc m) (hQ : ∀ m ∈ Q.support, inNQc m)
    (hJ : jac P Q = C lam * X 0 ^ 2)
    (hα : P.coeff (mono 8 14) ≠ 0) (hβ : Q.coeff (mono 12 21) ≠ 0)
    (hv : Q.coeff (mono 12 24) ≠ 0) : Q.coeff (mono 12 22) ≠ 0 := by
  intro ht
  obtain ⟨h35, h36, h37, -⟩ := edge19_eqs_of_jac lam P Q hP hQ hJ
  exact hv (edge19_t_zero _ _ _ _ _ _ _ hα hβ h35 h36 h37 ht)

end BranchC
