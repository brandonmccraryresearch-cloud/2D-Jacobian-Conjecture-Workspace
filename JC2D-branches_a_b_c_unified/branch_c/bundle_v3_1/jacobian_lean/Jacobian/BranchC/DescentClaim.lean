import Jacobian.BranchC.LayersGen
import Jacobian.BranchC.Edge19
import Jacobian.BranchAbTorus
import Jacobian.BranchAbChart
import Jacobian.ChartProof.Final

/-!
# Branch (c): the elimination modulo one computational claim (priority 4)

`DescentClaimC L` is the finite computational statement that the Gröbner basis step certifies: at the
rescaled K₅ top layer (`topA`, `topB`, the normalization of `certgen/cert.json`), in the chart `t₂ = 1`,
the layer identities `E₄, E₃, E₂, E₁, E₀, E₋₁, E₋₂` (`EIdent 4 … −2`) with the branch-(c) layer
supports have no solution.

It is **not proved in Lean**. It is a hypothesis (a `def … : Prop`, not an `axiom`), so every theorem that
uses it says so in its signature. Evidence (see `BRANCH_C_LEAN_STATUS.md`):

* the pipeline reduces it, by linear algebra over K₅ (the ranks `E₂ … E₋₂`: 18, 18, 17, 15, 13 of
  `branch_c/scripts/branch_c_stage2_e2_operator.py` … `branch_c_stage6c_e_minus2.py`), to six polynomial
  conditions `Ψ, Φ₁, Φ₂, Θ₁, Θ₂, Θ₃` in `(t₁, s₁, r₁, r₂, q)` after `t₂ = 1`, `s₂ = κ`
  (`branch_c/scripts/branch_c_stage6e_patch101.py`, corrected E₁ solve);
* Singular `slimgb` gives `⟨1⟩` for that system modulo 101 (and at further primes), and over K₅ exactly
  where the run finished.

Proved here (no `sorry`, no new axioms):

* `main_theorem_c_of_claim`: `DescentClaimC L → ` no branch-(c) pair `(P, Q)` with the ten vertices and
  `J(P,Q) = λx²` over `L` (char 0). The reduction uses `layers_of_jac_c` (all layer identities from the
  Jacobian), the top-layer classification of branch (a,b) (`topLayerClassification_of_chart`,
  `chartClassification_holds`; `E₅` and the top-layer supports are the same in branch (c)), the torus
  transport of all layers (`eIdent_transport`), the vertex–edge rigidity `vertex_12_24_forces_t2`
  (`t₂ ≠ 0`), and the weighted scaling `(A_k, B_l) ↦ (τ^{2−k} A_k, τ^{3−l} B_l)` that fixes the top layer
  and sends `t₂` to `1`.
-/

open MvPolynomial

noncomputable section

namespace BranchC

open BranchAb

variable {K : Type*} [Field K]

/-! ### The branch-(c) Newton polygons and layer supports -/

/-- Normal form (c): supports in `N(P)`, `N(Q)` and the ten vertex coefficients nonzero. -/
def NewtonNFc (P Q : MvPolynomial (Fin 2) K) : Prop :=
  (∀ m ∈ P.support, inNPc m) ∧ (∀ m ∈ Q.support, inNQc m) ∧
  P.coeff (mono 0 0) ≠ 0 ∧ P.coeff (mono 1 0) ≠ 0 ∧ P.coeff (mono 8 14) ≠ 0 ∧
  P.coeff (mono 8 16) ≠ 0 ∧ P.coeff (mono 0 8) ≠ 0 ∧
  Q.coeff (mono 0 0) ≠ 0 ∧ Q.coeff (mono 2 1) ≠ 0 ∧ Q.coeff (mono 12 21) ≠ 0 ∧
  Q.coeff (mono 12 24) ≠ 0 ∧ Q.coeff (mono 0 12) ≠ 0

/-- `xⁱ y^{2i−k} ∈ N(P)`: the exponents allowed in layer `k` of `P`. -/
def rangeP (k : ℤ) (i : ℕ) : Prop := k ≤ 2 * (i : ℤ) ∧ i ≤ 8 ∧ k ≤ 2 ∧ (i : ℤ) ≤ k + 8

/-- `xⁱ y^{2i−l} ∈ N(Q)`: the exponents allowed in layer `l` of `Q`. -/
def rangeQ (l : ℤ) (i : ℕ) : Prop :=
  l ≤ 2 * (i : ℤ) ∧ i ≤ 12 ∧ 2 * l ≤ 3 * (i : ℤ) ∧ l ≤ 3 ∧ (i : ℤ) ≤ l + 12

theorem support_layerZ_P (P : MvPolynomial (Fin 2) K) (hP : ∀ m ∈ P.support, inNPc m) (k : ℤ) (i : ℕ)
    (h : (layerZ P k).coeff i ≠ 0) : rangeP k i := by
  by_cases hlt : 2 * (i : ℤ) < k
  · exact absurd (coeff_layerZ_of_lt P k i hlt) h
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = 2 * i - k := ⟨(2 * (i : ℤ) - k).toNat, Int.toNat_of_nonneg (by omega)⟩
  rw [coeff_layerZ P k i j hj] at h
  have hm := hP _ (mem_support_iff.mpr h)
  simp only [inNPc, mono_apply_zero, mono_apply_one] at hm
  unfold rangeP
  omega

theorem support_layerZ_Q (Q : MvPolynomial (Fin 2) K) (hQ : ∀ m ∈ Q.support, inNQc m) (l : ℤ) (i : ℕ)
    (h : (layerZ Q l).coeff i ≠ 0) : rangeQ l i := by
  by_cases hlt : 2 * (i : ℤ) < l
  · exact absurd (coeff_layerZ_of_lt Q l i hlt) h
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = 2 * i - l := ⟨(2 * (i : ℤ) - l).toNat, Int.toNat_of_nonneg (by omega)⟩
  rw [coeff_layerZ Q l i j hj] at h
  have hm := hQ _ (mem_support_iff.mpr h)
  simp only [inNQc, mono_apply_zero, mono_apply_one] at hm
  unfold rangeQ
  omega

/-! ### The claim -/

/-- **The branch-(c) descent claim, chart `t₂ = 1`** (stated, not proved; priority 4). At the rescaled
K₅ top layer, the layer identities `E₄ … E₋₂` with the branch-(c) supports and `t₂ = b_{12,22} = 1` have no
solution. -/
def DescentClaimC (L : Type*) [Field L] : Prop :=
  ∀ (w : L), w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 = 0 →
  ∀ (A B : ℤ → Polynomial L),
    (∀ i, (A 2).coeff i = topA w i) → (∀ i, (B 3).coeff i = topB w i) →
    (∀ k i, (A k).coeff i ≠ 0 → rangeP k i) → (∀ l i, (B l).coeff i ≠ 0 → rangeQ l i) →
    (∀ n : ℤ, -2 ≤ n → n ≤ 4 → EIdent A B 0 n) →
    (B 2).coeff 12 = 1 → False

/-! ### Transport of the layer identities -/

lemma layerTermZ_sc (α β κ : K) (a b : ℤ) (A B : Polynomial K) :
    layerTermZ a b (Polynomial.C α * sc κ A) (Polynomial.C β * sc κ B) =
      Polynomial.C (α * β * κ) * sc κ (layerTermZ a b A B) := by
  simp only [layerTermZ, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    derivative_sc]
  simp only [sc, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.intCast_comp, Polynomial.C_mul]
  ring

lemma sc_sum (κ : K) {ι : Type*} (s : Finset ι) (f : ι → Polynomial K) :
    sc κ (∑ i ∈ s, f i) = ∑ i ∈ s, sc κ (f i) :=
  map_sum (Polynomial.compRingHom (Polynomial.C κ * Polynomial.X)) f s

lemma sc_zero (κ : K) : sc κ (0 : Polynomial K) = 0 := by simp [sc]

/-- **Torus and weighted-scaling transport.** For `n ≠ 5`, `EIdent n` is preserved by
`A_k ↦ α τ^{2−k} A_k(κu)`, `B_l ↦ β τ^{3−l} B_l(κu)` (every term of `EIdent n` is multiplied by
`α β τ^{5−n} κ`). -/
theorem eIdent_transport (A B : ℤ → Polynomial K) (lam lam' : K) (n : ℤ) (hn : n ≠ 5)
    (α β κ τ : K) (hτ : τ ≠ 0) (h : EIdent A B lam n) :
    EIdent (fun k => Polynomial.C (α * τ ^ (2 - k)) * sc κ (A k))
      (fun l => Polynomial.C (β * τ ^ (3 - l)) * sc κ (B l)) lam' n := by
  unfold EIdent at h ⊢
  rw [ite_eq_right_of_eq_false _ _ (eq_false hn)] at h ⊢
  have key : ∀ k : ℤ, (if n - k ∈ Finset.Icc (-12 : ℤ) 3 then
      layerTermZ k (n - k) (Polynomial.C (α * τ ^ (2 - k)) * sc κ (A k))
        (Polynomial.C (β * τ ^ (3 - (n - k))) * sc κ (B (n - k))) else 0) =
      Polynomial.C (α * β * τ ^ (5 - n) * κ) *
        sc κ (if n - k ∈ Finset.Icc (-12 : ℤ) 3 then layerTermZ k (n - k) (A k) (B (n - k)) else 0) := by
    intro k
    split_ifs
    · rw [layerTermZ_sc]
      have hz : τ ^ (2 - k) * τ ^ (3 - (n - k)) = τ ^ (5 - n) := by
        rw [← zpow_add₀ hτ]; ring_nf
      rw [show α * τ ^ (2 - k) * (β * τ ^ (3 - (n - k))) * κ = α * β * τ ^ (5 - n) * κ by
        rw [← hz]; ring]
    · rw [sc_zero, mul_zero]
  simp only at key ⊢
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, ← sc_sum, h, sc_zero, mul_zero]

/-! ### The main theorem, conditional on the claim -/

lemma coeff_C_mul_sc (c κ : K) (F : Polynomial K) (i : ℕ) :
    (Polynomial.C c * sc κ F).coeff i = c * (κ ^ i * F.coeff i) := by
  rw [Polynomial.coeff_C_mul, coeff_sc]

/-- **No branch-(c) pair, assuming `DescentClaimC`.** Over every field of characteristic `0` in which
`DescentClaimC` holds, there are no `P, Q` with the branch-(c) Newton polygons
`N(P) = conv{(0,0),(1,0),(8,14),(8,16),(0,8)}`, `N(Q) = conv{(0,0),(2,1),(12,21),(12,24),(0,12)}` and
`[P, Q] = λ x²`, `λ ≠ 0`. -/
theorem main_theorem_c_of_claim {L : Type*} [Field L] [CharZero L] (hD : DescentClaimC L) :
    ¬ ∃ (P Q : MvPolynomial (Fin 2) L) (lam : L), lam ≠ 0 ∧ NewtonNFc P Q ∧
      jac P Q = C lam * X 0 ^ 2 := by
  rintro ⟨P, Q, lam, -, ⟨hP, hQ, -, v10, v814, -, -, -, w21, w1221, w1224, -⟩, hJ⟩
  have hE := layers_of_jac_c lam P Q hP hQ hJ
  have E5 := eIdent_five _ _ _ (hE 5 (by norm_num))
  -- the top layer: supports, vertices, classification
  have sA₂ : ∀ i, (layerZ P 2).coeff i ≠ 0 → 1 ≤ i ∧ i ≤ 8 := fun i h => by
    have := support_layerZ_P P hP 2 i h; unfold rangeP at this; omega
  have sB₃ : ∀ i, (layerZ Q 3).coeff i ≠ 0 → 2 ≤ i ∧ i ≤ 12 := fun i h => by
    have := support_layerZ_Q Q hQ 3 i h; unfold rangeQ at this; omega
  have a1 : (layerZ P 2).coeff 1 ≠ 0 := by rw [coeff_layerZ P 2 1 0 (by norm_num)]; exact v10
  have a8 : (layerZ P 2).coeff 8 ≠ 0 := by rw [coeff_layerZ P 2 8 14 (by norm_num)]; exact v814
  have b2 : (layerZ Q 3).coeff 2 ≠ 0 := by rw [coeff_layerZ Q 3 2 1 (by norm_num)]; exact w21
  have b12 : (layerZ Q 3).coeff 12 ≠ 0 := by rw [coeff_layerZ Q 3 12 21 (by norm_num)]; exact w1221
  obtain ⟨w, ρ, σ, ε, hw, hρ, hσ, hε, hA, hB⟩ :=
    topLayerClassification_of_chart (chartClassification_holds L) _ _ lam sA₂ sB₃ a1 a8 b2 b12 E5
  -- `t₂ ≠ 0` from the vertex `(12,24)`
  have ht2 : (layerZ Q 2).coeff 12 ≠ 0 := by
    rw [coeff_layerZ Q 2 12 22 (by norm_num)]
    exact vertex_12_24_forces_t2 lam P Q hP hQ hJ v814 w1221 w1224
  -- transport to the rescaled K₅ point, then scale `t₂` to `1`
  have hβ : ε ^ 2 / σ ≠ 0 := div_ne_zero (pow_ne_zero 2 hε) hσ
  have hκ : ε⁻¹ ≠ 0 := inv_ne_zero hε
  have hτ' : ε ^ 2 / σ * ε⁻¹ ^ 12 * (layerZ Q 2).coeff 12 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hβ (pow_ne_zero 12 hκ)) ht2
  set τ := (ε ^ 2 / σ * ε⁻¹ ^ 12 * (layerZ Q 2).coeff 12)⁻¹ with hτdef
  have hτ : τ ≠ 0 := inv_ne_zero hτ'
  refine hD w hw (fun k => Polynomial.C (ε / ρ * τ ^ (2 - k)) * sc ε⁻¹ (layerZ P k))
    (fun l => Polynomial.C (ε ^ 2 / σ * τ ^ (3 - l)) * sc ε⁻¹ (layerZ Q l)) ?_ ?_ ?_ ?_ ?_ ?_
  · -- the top layer of `P`
    intro i
    rw [coeff_C_mul_sc, hA i, show (2 : ℤ) - 2 = 0 by norm_num, zpow_zero, mul_one]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [topA]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      have e1 : ε / ρ * (ε⁻¹ ^ (j + 1) * (ρ * ε ^ j)) = 1 := by
        rw [div_eq_mul_inv]
        calc ε * ρ⁻¹ * (ε⁻¹ ^ (j + 1) * (ρ * ε ^ j)) = (ρ * ρ⁻¹) * ((ε * ε ^ j) * ε⁻¹ ^ (j + 1)) := by
              ring
          _ = 1 := by
              rw [mul_inv_cancel₀ hρ, ← pow_succ', ← mul_pow, mul_inv_cancel₀ hε, one_pow, one_mul]
      calc ε / ρ * (ε⁻¹ ^ (j + 1) * (ρ * ε ^ j * topA w (j + 1)))
          = (ε / ρ * (ε⁻¹ ^ (j + 1) * (ρ * ε ^ j))) * topA w (j + 1) := by ring
        _ = topA w (j + 1) := by rw [e1, one_mul]
  · -- the top layer of `Q`
    intro k
    rw [coeff_C_mul_sc, hB k, show (3 : ℤ) - 3 = 0 by norm_num, zpow_zero, mul_one]
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k <;> simp [topB]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      rw [Nat.add_sub_cancel]
      have e1 : ε ^ 2 / σ * (ε⁻¹ ^ (j + 2) * (σ * ε ^ j)) = 1 := by
        rw [div_eq_mul_inv]
        calc ε ^ 2 * σ⁻¹ * (ε⁻¹ ^ (j + 2) * (σ * ε ^ j)) = (σ * σ⁻¹) * ((ε ^ j * ε ^ 2) * ε⁻¹ ^ (j + 2)) := by
              ring
          _ = 1 := by
              rw [mul_inv_cancel₀ hσ, ← pow_add, ← mul_pow, mul_inv_cancel₀ hε, one_pow, one_mul]
      calc ε ^ 2 / σ * (ε⁻¹ ^ (j + 2) * (σ * ε ^ j * topB w (j + 2)))
          = (ε ^ 2 / σ * (ε⁻¹ ^ (j + 2) * (σ * ε ^ j))) * topB w (j + 2) := by ring
        _ = topB w (j + 2) := by rw [e1, one_mul]
  · -- supports of the `P`-layers
    intro k i h
    simp only [coeff_C_mul_sc] at h
    exact support_layerZ_P P hP k i (right_ne_zero_of_mul (right_ne_zero_of_mul h))
  · -- supports of the `Q`-layers
    intro l i h
    simp only [coeff_C_mul_sc] at h
    exact support_layerZ_Q Q hQ l i (right_ne_zero_of_mul (right_ne_zero_of_mul h))
  · -- the layer identities `E₄ … E₋₂`
    intro n hn1 hn2
    exact eIdent_transport _ _ lam 0 n (by omega) _ _ _ _ hτ (hE n (by omega))
  · -- `t₂ = 1`
    rw [coeff_C_mul_sc, show (3 : ℤ) - 2 = 1 by norm_num, zpow_one]
    calc ε ^ 2 / σ * τ * (ε⁻¹ ^ 12 * (layerZ Q 2).coeff 12)
        = (ε ^ 2 / σ * ε⁻¹ ^ 12 * (layerZ Q 2).coeff 12) * τ := by ring
      _ = 1 := by rw [hτdef, mul_inv_cancel₀ hτ']

end BranchC
