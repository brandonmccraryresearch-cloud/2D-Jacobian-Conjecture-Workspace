import Jacobian.BranchC.LayerE2

/-!
# Branch (c): every layer identity from `[P,Q] = λx²`

For `P, Q` supported in the branch-(c) polygons, write `P = Σ_k y^{-k} A_k(u)`, `Q = Σ_l y^{-l} B_l(u)`
(`u = x y²`, `k ∈ [−8, 2]`, `l ∈ [−12, 3]`; `layerZ`). The bracket of two layers is
`[y^{-k} A(u), y^{-l} B(u)] = y^{1−k−l} LT_{k,l}(A,B)(u)` with `LT_{k,l}(A,B) = k A B′ − l A′ B`
(`layer_bracket_gen`, all signs of `k, l` at once), so the weight-`(n−1)` part of `J(P,Q) = λx²` is

  `EIdent n :  Σ_{k+l=n} LT_{k,l}(A_k, B_l) = [n = 5] · λu²`          (`layers_of_jac_c`).

`n = 5, 4, 3, 2, 1, 0, −1, −2` are the layers `E₅, E₄, E₃, E₂, E₁, E₀, E₋₁, E₋₂` of
`branch_c/scripts/branch_c_stage2_e2_operator.py` … `branch_c_stage6c_e_minus2.py`. `E2Identity`
(`Degree19.lean`) is `EIdent 2` (`eIdent_two`).

No `sorry`, no new axioms.
-/

open MvPolynomial

noncomputable section

namespace BranchC

open BranchAb

variable {K : Type*} [Field K]

/-! ### Layers with integer index -/

/-- Layer `k ∈ ℤ` of `P` as a polynomial in `u = x y²`: `layerPoly` for `k ≥ 0`, `layerPolyNeg` for `k < 0`. -/
def layerZ (P : MvPolynomial (Fin 2) K) (k : ℤ) : Polynomial K :=
  if 0 ≤ k then layerPoly P k.toNat else layerPolyNeg P (-k).toNat

/-- `(layerZ P k).coeff i = P.coeff (xⁱ y^{2i−k})` (and `0` if `2i < k`). -/
theorem coeff_layerZ (P : MvPolynomial (Fin 2) K) (k : ℤ) (i j : ℕ) (hj : (j : ℤ) = 2 * i - k) :
    (layerZ P k).coeff i = P.coeff (mono i j) := by
  unfold layerZ
  split_ifs with hk
  · have hk' : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
    rw [coeff_layerPoly_of_le P k.toNat i (by omega), show 2 * i - k.toNat = j by omega]
  · have hk' : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    rw [coeff_layerPolyNeg, show 2 * i + (-k).toNat = j by omega]

theorem coeff_layerZ_of_lt (P : MvPolynomial (Fin 2) K) (k : ℤ) (i : ℕ) (h : 2 * (i : ℤ) < k) :
    (layerZ P k).coeff i = 0 := by
  unfold layerZ
  have hk' : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
  split_ifs with h0
  · rw [coeff_layerPoly]
    split_ifs with h'
    · exfalso; omega
    · rfl
  · exfalso; omega

/-- `y^a · comp_k P = y^N · A_k(x y²)` whenever `a = N + k`. -/
lemma X1_pow_mul_comp_Z (P : MvPolynomial (Fin 2) K) (k : ℤ) (a N : ℕ) (h : (a : ℤ) = N + k) :
    X 1 ^ a * comp k P = X 1 ^ N * evH (layerZ P k) := by
  unfold layerZ
  split_ifs with hk
  · have hk' : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
    have ha : a = N + k.toNat := by omega
    rw [ha, pow_add, mul_assoc, ← X1_pow_mul_comp P k.toNat, hk']
  · have hj : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    have hN : N = a + (-k).toNat := by omega
    have hc : comp k P = X 1 ^ (-k).toNat * evH (layerPolyNeg P (-k).toNat) := by
      have := comp_neg P (-k).toNat
      rwa [hj, neg_neg] at this
    rw [hc, hN, pow_add, mul_assoc]

/-! ### The bracket of two layers, all signs -/

/-- `y^{a+b+1} J(p, q) = y^{N+M+2} · LT_{a−N, b−M}(A,B)(x y²)` when `yᵃ p = y^N A(x y²)` and
`y^b q = y^M B(x y²)`. -/
theorem layer_bracket_gen (a N b M : ℕ) (A B : Polynomial K) (p q : MvPolynomial (Fin 2) K)
    (hp : X 1 ^ a * p = X 1 ^ N * evH A) (hq : X 1 ^ b * q = X 1 ^ M * evH B) :
    X 1 ^ (a + b + 1) * jac p q =
      X 1 ^ (N + M + 2) * evH (layerTermZ ((a : ℤ) - N) ((b : ℤ) - M) A B) := by
  have d0 : ∀ (c n : ℕ) (r : MvPolynomial (Fin 2) K) (F : Polynomial K),
      X 1 ^ c * r = X 1 ^ n * evH F →
        X 1 ^ c * pderiv 0 r = X 1 ^ (n + 2) * evH (Polynomial.derivative F) := by
    intro c n r F h
    have := congrArg (pderiv 0) h
    rw [Derivation.leibniz, pderiv0_X1_pow, smul_zero, add_zero, smul_eq_mul, Derivation.leibniz,
      pderiv0_X1_pow, smul_zero, add_zero, smul_eq_mul, pderiv0_evH] at this
    rw [this]; ring
  have d1 : ∀ (c n : ℕ) (r : MvPolynomial (Fin 2) K) (F : Polynomial K),
      X 1 ^ c * r = X 1 ^ n * evH F →
        X 1 ^ (c + 1) * pderiv 1 r = X 1 ^ n * (((n : MvPolynomial (Fin 2) K) - (c : MvPolynomial (Fin 2) K)) * evH F +
          2 * uu * evH (Polynomial.derivative F)) := by
    intro c n r F h
    have h1 := congrArg (fun s => X 1 * pderiv 1 s) h
    simp only [Derivation.leibniz, smul_eq_mul, pderiv1_evH] at h1
    have ec := X1_mul_pderiv1_X1_pow (K := K) c
    have en := X1_mul_pderiv1_X1_pow (K := K) n
    rw [uu]
    linear_combination h1 - r * ec + evH F * en - (c : MvPolynomial (Fin 2) K) * h
  have hp0 := d0 a N p A hp
  have hq0 := d0 b M q B hq
  have hp1 := d1 a N p A hp
  have hq1 := d1 b M q B hq
  have hev : evH (layerTermZ ((a : ℤ) - N) ((b : ℤ) - M) A B) =
      ((a : MvPolynomial (Fin 2) K) - N) * (evH A * evH (Polynomial.derivative B)) -
        ((b : MvPolynomial (Fin 2) K) - M) * (evH (Polynomial.derivative A) * evH B) := by
    simp only [layerTermZ, map_sub, map_mul, map_intCast]
    push_cast
    ring
  rw [hev, jac]
  linear_combination (X 1 ^ (b + 1) * pderiv 1 q) * hp0 +
    (X 1 ^ (N + 2) * evH (Polynomial.derivative A)) * hq1 -
    (X 1 ^ b * pderiv 0 q) * hp1 -
    (X 1 ^ N * (((N : MvPolynomial (Fin 2) K) - a) * evH A + 2 * uu * evH (Polynomial.derivative A))) * hq0

/-! ### All layer identities -/

/-- **The weight-`(n−1)` layer identity** `Σ_{k+l=n} LT_{k,l}(A_k, B_l) = [n = 5] λu²`, summed over the
branch-(c) layer ranges `k ∈ [−8, 2]`, `l ∈ [−12, 3]`. -/
def EIdent (A B : ℤ → Polynomial K) (lam : K) (n : ℤ) : Prop :=
  ∑ k ∈ Finset.Icc (-8 : ℤ) 2,
      (if n - k ∈ Finset.Icc (-12 : ℤ) 3 then layerTermZ k (n - k) (A k) (B (n - k)) else 0) =
    if n = 5 then Polynomial.C lam * Polynomial.X ^ 2 else 0

private lemma cancel_X1' {m n : ℕ} {F G : MvPolynomial (Fin 2) K}
    (h : X 1 ^ (m + n) * F = X 1 ^ m * G) : X 1 ^ n * F = G := by
  have hne : (X 1 : MvPolynomial (Fin 2) K) ^ m ≠ 0 := pow_ne_zero _ (X_ne_zero 1)
  apply mul_left_cancel₀ hne
  rw [← mul_assoc, ← pow_add, h]

/-- **All layer identities of branch (c)** from `J(P,Q) = λx²`. -/
theorem layers_of_jac_c (lam : K) (P Q : MvPolynomial (Fin 2) K)
    (hP : ∀ m ∈ P.support, inNPc m) (hQ : ∀ m ∈ Q.support, inNQc m)
    (hJ : jac P Q = C lam * X 0 ^ 2) (n : ℤ) (hn : -20 ≤ n) :
    EIdent (layerZ P) (layerZ Q) lam n := by
  classical
  have hPs : ∀ d ∈ P.support, 2 * (d 0 : ℤ) - d 1 ∈ Finset.Icc (-8 : ℤ) 2 := by
    intro d hd; obtain ⟨h1, h2, h3⟩ := hP d hd; simp only [Finset.mem_Icc]; omega
  have hQs : ∀ d ∈ Q.support, 2 * (d 0 : ℤ) - d 1 ∈ Finset.Icc (-12 : ℤ) 3 := by
    intro d hd; obtain ⟨h1, h2, h3, h4⟩ := hQ d hd; simp only [Finset.mem_Icc]; omega
  -- the weight-(n−1) component of `J(P,Q)`
  have hsplit : comp (n - 1) (jac P Q) =
      ∑ k ∈ Finset.Icc (-8 : ℤ) 2, ∑ l ∈ Finset.Icc (-12 : ℤ) 3,
        if k + l - 1 = n - 1 then jac (comp k P) (comp l Q) else 0 := by
    conv_lhs => rw [eq_sum_comp P _ hPs, eq_sum_comp Q _ hQs, jac_sum_sum]
    simp only [map_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    have hkl := isWH_jac (isWH_comp k P) (isWH_comp l Q)
    split_ifs with h
    · rw [← h]; exact hkl.weightedHomogeneousComponent_same
    · exact hkl.weightedHomogeneousComponent_ne (n - 1) (Ne.symm h)
  have e : ∀ k : ℤ, (∑ l ∈ Finset.Icc (-12 : ℤ) 3,
      if k + l - 1 = n - 1 then jac (comp k P) (comp l Q) else 0) =
        if n - k ∈ Finset.Icc (-12 : ℤ) 3 then jac (comp k P) (comp (n - k) Q) else 0 := by
    intro k
    rw [← Finset.sum_ite_eq (Finset.Icc (-12 : ℤ) 3) (n - k) (fun l => jac (comp k P) (comp l Q))]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)
  obtain ⟨E, hE⟩ : ∃ E : ℕ, (E : ℤ) = 21 + n := ⟨(21 + n).toNat, Int.toNat_of_nonneg (by omega)⟩
  -- each pair, multiplied by `y^E`
  have key : ∀ k ∈ Finset.Icc (-8 : ℤ) 2, n - k ∈ Finset.Icc (-12 : ℤ) 3 →
      X 1 ^ E * jac (comp k P) (comp (n - k) Q) =
        X 1 ^ 22 * evH (layerTermZ k (n - k) (layerZ P k) (layerZ Q (n - k))) := by
    intro k hk hl
    simp only [Finset.mem_Icc] at hk hl
    obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = 8 + k := ⟨(8 + k).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨b, hb⟩ : ∃ b : ℕ, (b : ℤ) = 12 + (n - k) :=
      ⟨(12 + (n - k)).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hp := X1_pow_mul_comp_Z P k a 8 (by push_cast; omega)
    have hq := X1_pow_mul_comp_Z Q (n - k) b 12 (by push_cast; omega)
    have h := layer_bracket_gen a 8 b 12 _ _ _ _ hp hq
    have hab : a + b + 1 = E := by omega
    have hk' : (a : ℤ) - ((8 : ℕ) : ℤ) = k := by push_cast; omega
    have hl' : (b : ℤ) - ((12 : ℕ) : ℤ) = n - k := by push_cast; omega
    rw [hab, hk', hl'] at h
    rwa [show (8 + 12 + 2 : ℕ) = 22 from rfl] at h
  have hL : X 1 ^ E * comp (n - 1) (jac P Q) = X 1 ^ 22 * evH (∑ k ∈ Finset.Icc (-8 : ℤ) 2,
      (if n - k ∈ Finset.Icc (-12 : ℤ) 3 then
        layerTermZ k (n - k) (layerZ P k) (layerZ Q (n - k)) else 0)) := by
    rw [hsplit]
    simp only [e]
    rw [Finset.mul_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    split_ifs with hl
    · exact key k hk hl
    · simp
  have h4 : IsWeightedHomogeneous lw (C lam * X 0 ^ 2 : MvPolynomial (Fin 2) K) 4 := by
    convert (isWeightedHomogeneous_C lw lam).mul ((isWeightedHomogeneous_X K lw 0).pow 2) using 1
    simp [lw]
  have hR : X 1 ^ E * comp (n - 1) (C lam * X 0 ^ 2 : MvPolynomial (Fin 2) K) =
      X 1 ^ 22 * evH (if n = 5 then Polynomial.C lam * Polynomial.X ^ 2 else 0) := by
    split_ifs with h5
    · subst h5
      have hE26 : E = 26 := by omega
      have hc4 : comp ((5 : ℤ) - 1) (C lam * X 0 ^ 2 : MvPolynomial (Fin 2) K) = C lam * X 0 ^ 2 := by
        rw [show (5 : ℤ) - 1 = 4 by norm_num]; exact h4.weightedHomogeneousComponent_same
      rw [hE26, hc4]
      simp only [evH, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, uu,
        MvPolynomial.algebraMap_eq]
      ring
    · have hc : comp (n - 1) (C lam * X 0 ^ 2 : MvPolynomial (Fin 2) K) = 0 :=
        h4.weightedHomogeneousComponent_ne (n - 1) (by omega)
      rw [hc, mul_zero, map_zero, mul_zero]
  have h : X 1 ^ 22 * evH (∑ k ∈ Finset.Icc (-8 : ℤ) 2,
      (if n - k ∈ Finset.Icc (-12 : ℤ) 3 then
        layerTermZ k (n - k) (layerZ P k) (layerZ Q (n - k)) else 0)) =
      X 1 ^ 22 * evH (if n = 5 then Polynomial.C lam * Polynomial.X ^ 2 else 0) := by
    rw [← hL, ← hR, hJ]
  have h' := mul_left_cancel₀ (pow_ne_zero 22 (X_ne_zero (1 : Fin 2))) h
  unfold EIdent
  apply sub_eq_zero.mp
  apply evH_eq_zero
  rw [map_sub, h', sub_self]

/-! ### Reading off individual layers -/

/-- `EIdent 2` is the `E₂` identity of `Degree19.lean`. -/
theorem eIdent_two (A B : ℤ → Polynomial K) (lam : K) (h : EIdent A B lam 2) :
    E2Identity (A 2) (A 1) (A 0) (A (-1)) (B 3) (B 2) (B 1) (B 0) := by
  unfold EIdent at h
  rw [ite_eq_right_of_eq_false _ _ (eq_false (show (2 : ℤ) ≠ 5 by norm_num)), ← Finset.sum_filter] at h
  have hf : (Finset.Icc (-8 : ℤ) 2).filter (fun k => 2 - k ∈ Finset.Icc (-12 : ℤ) 3) = {-1, 0, 1, 2} := by
    decide
  rw [hf, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at h
  simp only [show (2 : ℤ) - -1 = 3 by norm_num, show (2 : ℤ) - 0 = 2 by norm_num,
    show (2 : ℤ) - 1 = 1 by norm_num, show (2 : ℤ) - 2 = 0 by norm_num] at h
  unfold E2Identity
  linear_combination h

/-- `EIdent 5` is the top-layer equation `2A₂B₃′ − 3A₂′B₃ = λu²`. -/
theorem eIdent_five (A B : ℤ → Polynomial K) (lam : K) (h : EIdent A B lam 5) :
    layerTerm 2 3 (A 2) (B 3) = Polynomial.C lam * Polynomial.X ^ 2 := by
  unfold EIdent at h
  rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), ← Finset.sum_filter] at h
  have hf : (Finset.Icc (-8 : ℤ) 2).filter (fun k => 5 - k ∈ Finset.Icc (-12 : ℤ) 3) = {2} := by
    decide
  rw [hf, Finset.sum_singleton, show (5 : ℤ) - 2 = 3 by norm_num] at h
  rw [← layerTermZ_natCast]
  exact_mod_cast h

end BranchC
