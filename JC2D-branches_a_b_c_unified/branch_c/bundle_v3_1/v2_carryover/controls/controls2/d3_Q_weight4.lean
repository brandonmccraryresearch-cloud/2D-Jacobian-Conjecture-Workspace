import Jacobian.BranchC.Degree19

/-!
# Branch (c): the weight-1 (`E₂`) layer identity from `[P,Q] = λx²`

Weight `w(xⁱ yʲ) = 2i − j` (the layer index). The bracket `J(p,q) = p_x q_y − p_y q_x` maps weights
`(a, b)` to `a + b − 1`. For `P, Q` supported in the branch-(c) polygons the weights of `P` lie in `[−8, 2]` and
those of `Q` in `[−12, 3]`, so the weight-1 part of `J(P,Q)` comes from exactly four layer pairs,
`(2,0), (1,1), (0,2), (−1,3)`, and `J(P,Q) = λx²` (weight 4) forces

  `LT_{2,0}(A₂,B₀) + LT_{1,1}(A₁,B₁) + LT_{0,2}(A₀,B₂) + LT_{−1,3}(A₋₁,B₃) = 0`

(`E2Identity`; `branch_c/scripts/branch_c_stage2_e2_operator.py`, lines 13–14). Combined with
`t0_vertex_rigidity` this gives `t0_vertex_rigidity_of_jac`: if `J(P,Q) = λx²` and `t = 0`
(`A₁ = 0`, `B₂ = 0`), then `b_{12,24} = 0`.

No `sorry`, no new axioms.
-/

open MvPolynomial

noncomputable section

namespace BranchC

open BranchAb

variable {K : Type*} [Field K]

/-! ### The layer weight -/

/-- `w(x) = 2`, `w(y) = −1`, so `w(xⁱ yʲ) = 2i − j`. -/
def lw : Fin 2 → ℤ := ![2, -1]

lemma weight_lw (d : Fin 2 →₀ ℕ) : Finsupp.weight lw d = 2 * (d 0 : ℤ) - d 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]
  simp [Fin.sum_univ_two, lw]
  ring

/-- `∂/∂xᵢ` lowers the weight by `w(xᵢ)`. -/
lemma isWH_pderiv {p : MvPolynomial (Fin 2) K} {a : ℤ} (hp : IsWeightedHomogeneous lw p a)
    (i : Fin 2) : IsWeightedHomogeneous lw (pderiv i p) (a - lw i) := by
  intro d hd
  rw [coeff_pderiv] at hd
  have h := hp (left_ne_zero_of_mul hd)
  rw [map_add, Finsupp.weight_single, one_smul] at h
  linarith

/-- The bracket maps weights `(a, b)` to `a + b − 1`. -/
lemma isWH_jac {p q : MvPolynomial (Fin 2) K} {a b : ℤ}
    (hp : IsWeightedHomogeneous lw p a) (hq : IsWeightedHomogeneous lw q b) :
    IsWeightedHomogeneous lw (jac p q) (a + b - 1) := by
  have h01 := (isWH_pderiv hp 0).mul (isWH_pderiv hq 1)
  have h10 := (isWH_pderiv hp 1).mul (isWH_pderiv hq 0)
  have e1 : a - lw 0 + (b - lw 1) = a + b - 1 := by simp [lw]; ring
  have e2 : a - lw 1 + (b - lw 0) = a + b - 1 := by simp [lw]; ring
  rw [e1] at h01
  rw [e2] at h10
  exact h01.sub h10

/-- The weight-`k` component. -/
abbrev comp (k : ℤ) (F : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  weightedHomogeneousComponent lw k F

lemma coeff_comp (k : ℤ) (F : MvPolynomial (Fin 2) K) (d : Fin 2 →₀ ℕ) :
    (comp k F).coeff d = if 2 * (d 0 : ℤ) - d 1 = k then F.coeff d else 0 := by
  rw [coeff_weightedHomogeneousComponent, weight_lw]

lemma isWH_comp (k : ℤ) (F : MvPolynomial (Fin 2) K) : IsWeightedHomogeneous lw (comp k F) k :=
  weightedHomogeneousComponent_isWeightedHomogeneous k F

/-- A polynomial whose weights lie in `s` is the sum of its components over `s`. -/
lemma eq_sum_comp (F : MvPolynomial (Fin 2) K) (s : Finset ℤ)
    (hs : ∀ d ∈ F.support, 2 * (d 0 : ℤ) - d 1 ∈ s) : F = ∑ k ∈ s, comp k F := by
  ext d
  rw [coeff_sum]
  simp only [coeff_comp]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hs d (mem_support_iff.mpr hne))

/-- The bracket is bilinear over finite sums. -/
lemma jac_sum_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (p : ι → MvPolynomial (Fin 2) K)
    (q : κ → MvPolynomial (Fin 2) K) :
    jac (∑ i ∈ s, p i) (∑ j ∈ t, q j) = ∑ i ∈ s, ∑ j ∈ t, jac (p i) (q j) := by
  simp only [jac, map_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]

/-! ### Components versus layer polynomials -/

/-- Every exponent is `xⁱ yʲ`. -/
private lemma eta (d : Fin 2 →₀ ℕ) : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
  ext i; fin_cases i <;> simp

/-- A component of nonnegative weight `a`: `y^a · comp a F = A_a(x y²)`. -/
lemma X1_pow_mul_comp (F : MvPolynomial (Fin 2) K) (a : ℕ) :
    X 1 ^ a * comp a F = evH (layerPoly F a) := by
  rw [← X1_pow_mul_layerPiece]
  congr 1
  ext d
  rw [coeff_comp]
  unfold layerPiece
  simp only [coeff_sum, coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter]
  by_cases hd : d ∈ F.support
  · split_ifs with h1 h2 h2
    · rfl
    · exact absurd ⟨hd, by omega⟩ h2
    · exact absurd (by omega) h1
    · rfl
  · have h0 : F.coeff d = 0 := notMem_support_iff.mp hd
    simp [h0]

/-- The weight-`(−k)` component: `comp (−k) F = y^k · A_{−k}(x y²)`. -/
lemma comp_neg (F : MvPolynomial (Fin 2) K) (k : ℕ) :
    comp (-(k : ℤ)) F = X 1 ^ k * evH (layerPolyNeg F k) := by
  ext d
  have hd := eta d
  rw [coeff_comp]
  conv_rhs => rw [hd]
  rw [coeff_yev, coeff_layerPolyNeg]
  split_ifs with h1 h2 h2
  · rw [show mono (d 0) (2 * d 0 + k) = d by rw [← h2]; exact mono_eta d]
  · exfalso; omega
  · exfalso; omega
  · rfl

/-! ### The bracket of a negative layer with a nonnegative one -/

/-- `y^{b+1} J(y^c A(x y²), q) = y^{c+2} · LT_{−c,b}(A,B)(x y²)` when `y^b q = B(x y²)`. -/
theorem layer_bracket_neg (c b : ℕ) (A B : Polynomial K) (q : MvPolynomial (Fin 2) K)
    (hq : X 1 ^ b * q = evH B) :
    X 1 ^ (b + 1) * jac (X 1 ^ c * evH A) q =
      X 1 ^ (c + 2) * evH (layerTermZ (-(c : ℤ)) b A B) := by
  -- derivatives of `q`
  have hq0 : X 1 ^ b * pderiv 0 q = evH (Polynomial.derivative B) * X 1 ^ 2 := by
    have := congrArg (pderiv 0) hq
    rw [Derivation.leibniz, pderiv0_X1_pow, smul_zero, add_zero, smul_eq_mul, pderiv0_evH] at this
    exact this
  have hq1 : X 1 ^ (b + 1) * pderiv 1 q =
      2 * uu * evH (Polynomial.derivative B) - (b : MvPolynomial (Fin 2) K) * evH B := by
    have h1 := congrArg (fun s => X 1 * pderiv 1 s) hq
    simp only [Derivation.leibniz, smul_eq_mul, pderiv1_evH] at h1
    have e := X1_mul_pderiv1_X1_pow (K := K) b
    rw [← hq, uu]
    linear_combination h1 - q * e
  -- derivatives of `p = y^c A(x y²)`
  have hp0 : pderiv 0 (X 1 ^ c * evH A) = X 1 ^ (c + 2) * evH (Polynomial.derivative A) := by
    rw [Derivation.leibniz, pderiv0_X1_pow, smul_zero, add_zero, smul_eq_mul, pderiv0_evH]
    ring
  have hp1 : X 1 * pderiv 1 (X 1 ^ c * evH A) =
      X 1 ^ c * ((c : MvPolynomial (Fin 2) K) * evH A + 2 * uu * evH (Polynomial.derivative A)) := by
    have e := X1_mul_pderiv1_X1_pow (K := K) c
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv1_evH, uu]
    linear_combination evH A * e
  have hev : evH (layerTermZ (-(c : ℤ)) b A B) =
      -(c : MvPolynomial (Fin 2) K) * (evH A * evH (Polynomial.derivative B)) -
        (b : MvPolynomial (Fin 2) K) * (evH (Polynomial.derivative A) * evH B) := by
    simp only [layerTermZ, map_sub, map_mul, Int.cast_neg, Int.cast_natCast, map_neg, map_natCast]
    ring
  rw [hev, jac]
  linear_combination (pderiv 0 (X 1 ^ c * evH A)) * hq1 +
    (2 * uu * evH (Polynomial.derivative B) - (b : MvPolynomial (Fin 2) K) * evH B) * hp0 -
    (X 1 ^ b * pderiv 0 q) * hp1 -
    (X 1 ^ c * ((c : MvPolynomial (Fin 2) K) * evH A + 2 * uu * evH (Polynomial.derivative A))) * hq0

/-- Cancel a power of `y`. -/
private lemma cancel_X1 {m n : ℕ} {F G : MvPolynomial (Fin 2) K}
    (h : X 1 ^ (m + n) * F = X 1 ^ m * G) : X 1 ^ n * F = G := by
  have hne : (X 1 : MvPolynomial (Fin 2) K) ^ m ≠ 0 := pow_ne_zero _ (X_ne_zero 1)
  apply mul_left_cancel₀ hne
  rw [← mul_assoc, ← pow_add, h]

/-- `A(x y²) = 0` forces `A = 0`. -/
lemma evH_eq_zero {F : Polynomial K} (h : evH F = 0) : F = 0 := by
  ext i
  have := coeff_yev F 0 i (2 * i)
  rw [pow_zero, one_mul, h] at this
  simpa using this.symm

/-! ### The weight-1 identity -/

/-- **Branch-(c) layer reduction at weight 1.** If `P, Q` are supported in the branch-(c) polygons and
`J(P,Q) = λx²`, their layers satisfy the `E₂` identity. -/
theorem e2Identity_of_jac (lam : K) (P Q : MvPolynomial (Fin 2) K)
    (hP : ∀ m ∈ P.support, inNPc m) (hQ : ∀ m ∈ Q.support, inNQc m)
    (hJ : jac P Q = C lam * X 0 ^ 2) :
    E2Identity (layerPoly P 2) (layerPoly P 1) (layerPoly P 0) (layerPolyNeg P 1)
      (layerPoly Q 3) (layerPoly Q 2) (layerPoly Q 1) (layerPoly Q 0) := by
  classical
  -- weights of `P` in `[−8, 2]`, of `Q` in `[−12, 3]`
  have hPs : ∀ d ∈ P.support, 2 * (d 0 : ℤ) - d 1 ∈ Finset.Icc (-8 : ℤ) 2 := by
    intro d hd; obtain ⟨h1, h2, h3⟩ := hP d hd; simp only [Finset.mem_Icc]; omega
  have hQs : ∀ d ∈ Q.support, 2 * (d 0 : ℤ) - d 1 ∈ Finset.Icc (-12 : ℤ) 3 := by
    intro d hd; obtain ⟨h1, h2, h3, h4⟩ := hQ d hd; simp only [Finset.mem_Icc]; omega
  have hQs4 : ∀ d ∈ Q.support, 2 * (d 0 : ℤ) - d 1 ∈ Finset.Icc (-12 : ℤ) 4 := by
    intro d hd; have := hQs d hd; simp only [Finset.mem_Icc] at this ⊢; omega
  -- the weight-1 component of `J(P,Q)`
  have hsplit : comp 1 (jac P Q) =
      ∑ k ∈ Finset.Icc (-8 : ℤ) 2, ∑ l ∈ Finset.Icc (-12 : ℤ) 4,
        if k + l - 1 = 1 then jac (comp k P) (comp l Q) else 0 := by
    conv_lhs => rw [eq_sum_comp P _ hPs, eq_sum_comp Q _ hQs4, jac_sum_sum]
    simp only [map_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    have hkl := isWH_jac (isWH_comp k P) (isWH_comp l Q)
    split_ifs with h
    · rw [← h]; exact hkl.weightedHomogeneousComponent_same
    · exact hkl.weightedHomogeneousComponent_ne 1 (Ne.symm h)
  have hpairs : comp 1 (jac P Q) =
      jac (comp 2 P) (comp 0 Q) + jac (comp 1 P) (comp 1 Q) + jac (comp 0 P) (comp 2 Q) +
        jac (comp (-1) P) (comp 3 Q) := by
    rw [hsplit]
    have e : ∀ k : ℤ, (∑ l ∈ Finset.Icc (-12 : ℤ) 4,
        if k + l - 1 = 1 then jac (comp k P) (comp l Q) else 0) =
          if 2 - k ∈ Finset.Icc (-12 : ℤ) 4 then jac (comp k P) (comp (2 - k) Q) else 0 := by
      intro k
      rw [← Finset.sum_ite_eq (Finset.Icc (-12 : ℤ) 4) (2 - k) (fun l => jac (comp k P) (comp l Q))]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)
    simp only [e]
    rw [← Finset.sum_filter]
    have hf : (Finset.Icc (-8 : ℤ) 2).filter (fun k => 2 - k ∈ Finset.Icc (-12 : ℤ) 4) =
        {-1, 0, 1, 2} := by decide
    rw [hf]
    simp [Finset.sum_insert, Finset.mem_insert]
    ring
  -- the weight-1 component of `λx²` vanishes
  have htgt : comp 1 (C lam * X 0 ^ 2 : MvPolynomial (Fin 2) K) = 0 := by
    have h4 : IsWeightedHomogeneous lw (C lam * X 0 ^ 2 : MvPolynomial (Fin 2) K) (0 + 2 • lw 0) :=
      (isWeightedHomogeneous_C lw lam).mul ((isWeightedHomogeneous_X K lw 0).pow 2)
    exact h4.weightedHomogeneousComponent_ne 1 (by simp [lw])
  -- the four brackets, as `y⁻¹ · LT(x y²)`
  have b20 := cancel_X1 (m := 2) (n := 1) (by
    have := layer_bracket 2 0 (layerPoly P 2) (layerPoly Q 0) (comp 2 P) (comp 0 Q)
      (X1_pow_mul_comp P 2) (by simpa using X1_pow_mul_comp Q 0)
    simpa using this)
  have b11 := cancel_X1 (m := 2) (n := 1) (by
    have := layer_bracket 1 1 (layerPoly P 1) (layerPoly Q 1) (comp 1 P) (comp 1 Q)
      (by simpa using X1_pow_mul_comp P 1) (by simpa using X1_pow_mul_comp Q 1)
    simpa using this)
  have b02 := cancel_X1 (m := 2) (n := 1) (by
    have := layer_bracket 0 2 (layerPoly P 0) (layerPoly Q 2) (comp 0 P) (comp 2 Q)
      (by simpa using X1_pow_mul_comp P 0) (X1_pow_mul_comp Q 2)
    simpa using this)
  have bm13 : X 1 ^ 1 * jac (comp (-1) P) (comp 3 Q) =
      evH (layerTermZ (-1) 3 (layerPolyNeg P 1) (layerPoly Q 3)) := by
    have hc : comp (-1) P = X 1 ^ 1 * evH (layerPolyNeg P 1) := by
      simpa using comp_neg P 1
    have := layer_bracket_neg 1 3 (layerPolyNeg P 1) (layerPoly Q 3) (comp 3 Q) (X1_pow_mul_comp Q 3)
    rw [← hc] at this
    exact cancel_X1 (m := 3) (n := 1) (by simpa using this)
  -- assemble
  have hE : evH (layerTermZ 2 0 (layerPoly P 2) (layerPoly Q 0) +
      layerTermZ 1 1 (layerPoly P 1) (layerPoly Q 1) + layerTermZ 0 2 (layerPoly P 0) (layerPoly Q 2) +
      layerTermZ (-1) 3 (layerPolyNeg P 1) (layerPoly Q 3)) = 0 := by
    have h0 : X 1 ^ 1 * comp 1 (jac P Q) = 0 := by rw [hJ, htgt, mul_zero]
    rw [hpairs] at h0
    have e20 : layerTermZ (2 : ℤ) 0 (layerPoly P 2) (layerPoly Q 0) =
        layerTerm 2 0 (layerPoly P 2) (layerPoly Q 0) := by exact_mod_cast layerTermZ_natCast 2 0 _ _
    have e11 : layerTermZ (1 : ℤ) 1 (layerPoly P 1) (layerPoly Q 1) =
        layerTerm 1 1 (layerPoly P 1) (layerPoly Q 1) := by exact_mod_cast layerTermZ_natCast 1 1 _ _
    have e02 : layerTermZ (0 : ℤ) 2 (layerPoly P 0) (layerPoly Q 2) =
        layerTerm 0 2 (layerPoly P 0) (layerPoly Q 2) := by exact_mod_cast layerTermZ_natCast 0 2 _ _
    rw [map_add, map_add, map_add, e20, e11, e02, ← b20, ← b11, ← b02, ← bm13]
    rw [← h0]
    ring
  exact evH_eq_zero hE

/-- **Degree-19 Rigidity for `[P,Q] = λx²`.** If `P, Q` are supported in the branch-(c) polygons,
`a_{8,14} ≠ 0`, `J(P,Q) = λx²`, and `t = 0` (`A₁ = 0`, `B₂ = 0`), then `b_{12,24} = 0`, so `(12,24)`
is not a vertex of `N(Q)`. -/
theorem t0_vertex_rigidity_of_jac [CharZero K] (lam : K) (P Q : MvPolynomial (Fin 2) K)
    (hP : ∀ m ∈ P.support, inNPc m) (hQ : ∀ m ∈ Q.support, inNQc m)
    (h814 : P.coeff (mono 8 14) ≠ 0) (hJ : jac P Q = C lam * X 0 ^ 2)
    (ht : layerPoly P 1 = 0 ∧ layerPoly Q 2 = 0) :
    Q.coeff (mono 12 24) = 0 :=
  t0_vertex_rigidity P Q hP hQ h814 (e2Identity_of_jac lam P Q hP hQ hJ) ht

end BranchC
