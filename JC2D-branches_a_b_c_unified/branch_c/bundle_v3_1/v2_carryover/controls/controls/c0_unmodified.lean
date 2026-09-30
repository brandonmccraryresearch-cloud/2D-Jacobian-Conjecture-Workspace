import Jacobian.BranchAbNewton

/-!
# Branch (c): the Degree-19 Rigidity Lemma

GGHV Proposition 4.3, case (1) (arXiv:2204.14178v1, Prop. 4.3(1); `branch_c/README.md`),
degree pair `(72,108)`:

  `N(P) = conv{(0,0),(1,0),(8,14),(8,16),(0,8)}`,  `N(Q) = conv{(0,0),(2,1),(12,21),(12,24),(0,12)}`.

With `u = x y²` and the layers `P = Σ_k y^{-k} A_k(u)`, `Q = Σ_l y^{-l} B_l(u)` (`k = 2i − j`, as in
`branch_c/scripts/branch_c_stage1_setup.py`), the weight-1 layer identity (`E₂` in
`branch_c/scripts/branch_c_stage2_e2_operator.py`, lines 13–14) is

  `LT_{2,0}(A₂,B₀) + LT_{1,1}(A₁,B₁) + LT_{0,2}(A₀,B₂) + LT_{−1,3}(A₋₁,B₃) = 0`,
  `LT_{a,b}(A,B) = a·A·B′ − b·A′·B`.

At `t = 0` the `E₄` kernel direction vanishes, `A₁ = 0` and `B₂ = 0`, and the identity becomes
`2·A₂·B₀′ = A₋₁·B₃′ + 3·A₋₁′·B₃`. Its `u¹⁹` coefficient is `24·a_{8,14}·b_{12,24} = 0`: the left side
has degree `8 + 11 = 19`, while `deg A₋₁ ≤ 7` caps the right side at `u¹⁸`.

## Contents (no `sorry`, no new axioms)

* `degree19_rigidity` — the lemma for polynomials in `u`.
* `e2_t0_rigidity` — the same from the full `E₂` identity with `A₁ = 0`, `B₂ = 0`.
* `t0_vertex_rigidity` — for `P, Q ∈ K[x,y]` supported in the branch-(c) polygons. The layer
  polynomials are read off the coefficients of `P` and `Q`, the degree bounds are derived from the
  polygons, and the conclusion is `Q.coeff (x¹² y²⁴) = 0`, so `(12,24)` is not a vertex of `N(Q)`.
* `degree19_bound_sharp` — control: with `deg A₋₁ ≤ 8` instead of `≤ 7` the conclusion fails.
* `latticeNPc_card`, `latticeNQc_card`, `verticesc_mem` — the half-plane predicates against the lattice
  counts `61` and `125` of `branch_c_stage1_setup.py`, and the ten vertices.

## What is assumed

The `E₂` identity itself (`E2Identity`) is a hypothesis of `e2_t0_rigidity` and `t0_vertex_rigidity`.
Deriving it from `[P,Q] = λx²` is the branch-(c) analogue of `BranchAb.layers_of_jac` and is not
formalized here. The hypothesis `t = 0` is stated as `A₁ = 0 ∧ B₂ = 0`, i.e. the `E₄` kernel coordinates
`(A₁, B₂) = t₁ v₁ + t₂ v₂` vanish (the `E₅`, `E₄`, `E₃` layers of branch (c) coincide with branch (a,b),
`branch_c_stage1_setup.py`).
-/

open MvPolynomial

noncomputable section

namespace BranchC

open BranchAb

variable {K : Type*} [Field K]

/-! ### The branch-(c) Newton polygons -/

/-- `(i, j) ∈ N(P) = conv{(0,0),(1,0),(8,14),(8,16),(0,8)}`: `i ≤ 8`, `j ≥ 2i − 2`, `j ≤ i + 8`
(`i, j ≥ 0` are automatic). -/
def inNPc (m : Fin 2 →₀ ℕ) : Prop := m 0 ≤ 8 ∧ 2 * m 0 ≤ m 1 + 2 ∧ m 1 ≤ m 0 + 8

/-- `(i, j) ∈ N(Q) = conv{(0,0),(2,1),(12,21),(12,24),(0,12)}`: `i ≤ 12`, `i ≤ 2j`, `j ≥ 2i − 3`,
`j ≤ i + 12`. -/
def inNQc (m : Fin 2 →₀ ℕ) : Prop := m 0 ≤ 12 ∧ m 0 ≤ 2 * m 1 ∧ 2 * m 0 ≤ m 1 + 3 ∧ m 1 ≤ m 0 + 12

/-- The lattice points of the half-plane systems (sanity check against the scripts). -/
def latticeNPc : Finset (ℕ × ℕ) :=
  (Finset.range 13 ×ˢ Finset.range 25).filter
    (fun p => p.1 ≤ 8 ∧ 2 * p.1 ≤ p.2 + 2 ∧ p.2 ≤ p.1 + 8)
def latticeNQc : Finset (ℕ × ℕ) :=
  (Finset.range 13 ×ˢ Finset.range 25).filter
    (fun p => p.1 ≤ 12 ∧ p.1 ≤ 2 * p.2 ∧ 2 * p.1 ≤ p.2 + 3 ∧ p.2 ≤ p.1 + 12)

/-- `61` and `125` lattice points, as in `branch_c_stage1_setup.py` (Pick's theorem cross-check there). -/
theorem latticeNPc_card : latticeNPc.card = 61 := by decide
theorem latticeNQc_card : latticeNQc.card = 125 := by decide +kernel

/-- The ten vertices lie on the polygons. -/
theorem verticesc_mem :
    (0, 0) ∈ latticeNPc ∧ (1, 0) ∈ latticeNPc ∧ (8, 14) ∈ latticeNPc ∧ (8, 16) ∈ latticeNPc ∧
    (0, 8) ∈ latticeNPc ∧ (0, 0) ∈ latticeNQc ∧ (2, 1) ∈ latticeNQc ∧ (12, 21) ∈ latticeNQc ∧
    (12, 24) ∈ latticeNQc ∧ (0, 12) ∈ latticeNQc := by decide

/-! ### Layers with negative index and the integer layer operator -/

/-- Layer `−k` of `P`: the monomials `xⁱ yʲ` with `j = 2i + k`, as a polynomial in `u = x y²`
(so the layer-`(−k)` piece of `P` is `y^k · A_{−k}(x y²)`). Layers `a ≥ 0` are `BranchAb.layerPoly`. -/
def layerPolyNeg (P : MvPolynomial (Fin 2) K) (k : ℕ) : Polynomial K :=
  ∑ m ∈ P.support.filter (fun m => m 1 = 2 * m 0 + k), Polynomial.monomial (m 0) (P.coeff m)

theorem coeff_layerPolyNeg (P : MvPolynomial (Fin 2) K) (k i : ℕ) :
    (layerPolyNeg P k).coeff i = P.coeff (mono i (2 * i + k)) := by
  unfold layerPolyNeg
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_filter]
  have key : ∀ m : Fin 2 →₀ ℕ, (m 1 = 2 * m 0 + k ∧ m 0 = i) ↔ m = mono i (2 * i + k) := by
    intro m
    constructor
    · rintro ⟨h1, rfl⟩
      ext j; fin_cases j <;> simp; omega
    · rintro rfl; simp
  simp only [← ite_and, key]
  rw [Finset.sum_ite_eq']
  split_ifs with hs
  · rfl
  · exact (notMem_support_iff.mp hs).symm

/-- `LT_{a,b}(A,B) = a·A·B′ − b·A′·B` with integer layer indices. -/
def layerTermZ (a b : ℤ) (A B : Polynomial K) : Polynomial K :=
  (a : Polynomial K) * A * Polynomial.derivative B - (b : Polynomial K) * Polynomial.derivative A * B

/-- On natural-number indices `layerTermZ` is `BranchAb.layerTerm`. -/
theorem layerTermZ_natCast (a b : ℕ) (A B : Polynomial K) :
    layerTermZ a b A B = layerTerm a b A B := by
  simp [layerTermZ, layerTerm]

/-- The weight-1 (`E₂`) layer identity of branch (c):
`LT_{2,0}(A₂,B₀) + LT_{1,1}(A₁,B₁) + LT_{0,2}(A₀,B₂) + LT_{−1,3}(A₋₁,B₃) = 0`
(`branch_c_stage2_e2_operator.py`, lines 13–14, with `RHS_{E₂}` moved to the left). -/
def E2Identity (A₂ A₁ A₀ Am1 B₃ B₂ B₁ B₀ : Polynomial K) : Prop :=
  layerTermZ 2 0 A₂ B₀ + layerTermZ 1 1 A₁ B₁ + layerTermZ 0 2 A₀ B₂ + layerTermZ (-1) 3 Am1 B₃ = 0

/-! ### The lemma -/

/-- **Degree-19 Rigidity** (polynomial form). If `2·A₂·B₀′ = A₋₁·B₃′ + 3·A₋₁′·B₃` with
`deg A₂ ≤ 8`, `deg B₀ ≤ 12`, `deg A₋₁ ≤ 7`, `deg B₃ ≤ 12` and `[u⁸]A₂ ≠ 0`, then `[u¹²]B₀ = 0`:
the `u¹⁹` coefficient of the left side is `24·[u⁸]A₂·[u¹²]B₀`, and the right side has degree `≤ 18`. -/
theorem degree19_rigidity [CharZero K] (A₂ Am1 B₀ B₃ : Polynomial K)
    (hA₂ : A₂.natDegree ≤ 8) (hB₀ : B₀.natDegree ≤ 12)
    (hAm1 : Am1.natDegree ≤ 7) (hB₃ : B₃.natDegree ≤ 12)
    (hlead : A₂.coeff 8 ≠ 0)
    (hE : 2 * A₂ * Polynomial.derivative B₀ =
      Am1 * Polynomial.derivative B₃ + 3 * Polynomial.derivative Am1 * B₃) :
    B₀.coeff 12 = 0 := by
  have hB₀' : (Polynomial.derivative B₀).natDegree ≤ 11 :=
    (Polynomial.natDegree_derivative_le B₀).trans (by omega)
  have hB₃' : (Polynomial.derivative B₃).natDegree ≤ 11 :=
    (Polynomial.natDegree_derivative_le B₃).trans (by omega)
  have hAm1' : (Polynomial.derivative Am1).natDegree ≤ 6 :=
    (Polynomial.natDegree_derivative_le Am1).trans (by omega)
  -- the `u¹⁹` coefficient of the left side
  have hL : (2 * A₂ * Polynomial.derivative B₀).coeff 19 = 2 * (A₂.coeff 8 * (B₀.coeff 12 * 12)) := by
    rw [mul_assoc, Polynomial.coeff_ofNat_mul, show (19 : ℕ) = 8 + 11 from rfl,
      Polynomial.coeff_mul_add_eq_of_natDegree_le hA₂ hB₀', Polynomial.coeff_derivative]
    norm_num
  -- the right side has degree `≤ 18`
  have hR : (Am1 * Polynomial.derivative B₃ + 3 * Polynomial.derivative Am1 * B₃).coeff 19 = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have h1 : (Am1 * Polynomial.derivative B₃).natDegree ≤ 18 :=
      Polynomial.natDegree_mul_le.trans (by omega)
    have h3 : (3 * Polynomial.derivative Am1 : Polynomial K).natDegree ≤ 6 :=
      Polynomial.natDegree_mul_le.trans (by rw [Polynomial.natDegree_ofNat]; omega)
    have h2 : (3 * Polynomial.derivative Am1 * B₃).natDegree ≤ 18 :=
      Polynomial.natDegree_mul_le.trans (by omega)
    exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (by omega)
  have h := congrArg (fun p => Polynomial.coeff p 19) hE
  rw [hL, hR] at h
  simpa [hlead] using h

/-- The lemma from the full `E₂` identity at `t = 0` (`A₁ = 0`, `B₂ = 0`). -/
theorem e2_t0_rigidity [CharZero K] (A₂ A₁ A₀ Am1 B₃ B₂ B₁ B₀ : Polynomial K)
    (hA₂ : A₂.natDegree ≤ 8) (hB₀ : B₀.natDegree ≤ 12)
    (hAm1 : Am1.natDegree ≤ 7) (hB₃ : B₃.natDegree ≤ 12)
    (hlead : A₂.coeff 8 ≠ 0)
    (hE₂ : E2Identity A₂ A₁ A₀ Am1 B₃ B₂ B₁ B₀) (ht : A₁ = 0 ∧ B₂ = 0) :
    B₀.coeff 12 = 0 := by
  obtain ⟨rfl, rfl⟩ := ht
  refine degree19_rigidity A₂ Am1 B₀ B₃ hA₂ hB₀ hAm1 hB₃ hlead ?_
  simp only [E2Identity, layerTermZ, Polynomial.derivative_zero, mul_zero, zero_mul, sub_zero,
    Int.cast_zero, Int.cast_one, Int.cast_neg, Int.cast_ofNat] at hE₂
  linear_combination hE₂

/-! ### For `P, Q ∈ K[x,y]` with the branch-(c) polygons -/

/-- A layer polynomial has degree `≤ N` when its coefficients above `N` vanish. -/
private lemma natDegree_le_of_coeff {F : Polynomial K} {N : ℕ} (h : ∀ i, N < i → F.coeff i = 0) :
    F.natDegree ≤ N :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun i hi => h i (by exact_mod_cast hi))

/-- **Degree-19 Rigidity for `P, Q`.** Let `P, Q` be supported in the branch-(c) polygons with
`a_{8,14} ≠ 0`. If the `E₂` identity holds for their layers and `t = 0` (`A₁ = 0`, `B₂ = 0`), then
`b_{12,24} = 0`, so `(12,24)` is not a vertex of `N(Q)`. -/
theorem t0_vertex_rigidity [CharZero K] (P Q : MvPolynomial (Fin 2) K)
    (hP : ∀ m ∈ P.support, inNPc m) (hQ : ∀ m ∈ Q.support, inNQc m)
    (h814 : P.coeff (mono 8 14) ≠ 0)
    (hE₂ : E2Identity (layerPoly P 2) (layerPoly P 1) (layerPoly P 0) (layerPolyNeg P 1)
      (layerPoly Q 3) (layerPoly Q 2) (layerPoly Q 1) (layerPoly Q 0))
    (ht : layerPoly P 1 = 0 ∧ layerPoly Q 2 = 0) :
    Q.coeff (mono 12 24) = 0 := by
  -- coefficients outside the polygons vanish
  have zP : ∀ m, ¬ inNPc m → P.coeff m = 0 := fun m hm =>
    notMem_support_iff.mp (fun h => hm (hP m h))
  have zQ : ∀ m, ¬ inNQc m → Q.coeff m = 0 := fun m hm =>
    notMem_support_iff.mp (fun h => hm (hQ m h))
  -- degree bounds from the polygons
  have hA₂ : (layerPoly P 2).natDegree ≤ 8 := natDegree_le_of_coeff fun i hi => by
    rw [coeff_layerPoly]; split_ifs
    · exact zP _ (by simp [inNPc]; omega)
    · rfl
  have hB₀ : (layerPoly Q 0).natDegree ≤ 12 := natDegree_le_of_coeff fun i hi => by
    rw [coeff_layerPoly]; split_ifs
    · exact zQ _ (by simp [inNQc]; omega)
    · rfl
  have hAm1 : (layerPolyNeg P 1).natDegree ≤ 7 := natDegree_le_of_coeff fun i hi => by
    rw [coeff_layerPolyNeg]
    exact zP _ (by simp [inNPc]; omega)
  have hB₃ : (layerPoly Q 3).natDegree ≤ 12 := natDegree_le_of_coeff fun i hi => by
    rw [coeff_layerPoly]; split_ifs
    · exact zQ _ (by simp [inNQc]; omega)
    · rfl
  have hlead : (layerPoly P 2).coeff 8 ≠ 0 := by
    rw [coeff_layerPoly_of_le P 2 8 (by norm_num)]; exact h814
  have h := e2_t0_rigidity _ _ _ _ _ _ _ _ hA₂ hB₀ hAm1 hB₃ hlead hE₂ ht
  rwa [coeff_layerPoly_of_le Q 0 12 (by norm_num)] at h

/-! ### Control: the bound `deg A₋₁ ≤ 7` is sharp -/

/-- With `deg A₋₁ ≤ 8` allowed, the conclusion fails: `A₂ = 3u⁸`, `A₋₁ = 2u⁸`, `B₃ = u¹²`, `B₀ = u¹²`
satisfy `2·A₂·B₀′ = A₋₁·B₃′ + 3·A₋₁′·B₃` (both sides `72·u¹⁹`) with `[u¹²]B₀ = 1`. -/
theorem degree19_bound_sharp :
    ∃ A₂ Am1 B₀ B₃ : Polynomial ℚ,
      A₂.natDegree ≤ 8 ∧ B₀.natDegree ≤ 12 ∧ Am1.natDegree ≤ 8 ∧ B₃.natDegree ≤ 12 ∧
      A₂.coeff 8 ≠ 0 ∧
      2 * A₂ * Polynomial.derivative B₀ =
        Am1 * Polynomial.derivative B₃ + 3 * Polynomial.derivative Am1 * B₃ ∧
      B₀.coeff 12 ≠ 0 := by
  refine ⟨3 * Polynomial.X ^ 8, 2 * Polynomial.X ^ 8, Polynomial.X ^ 12, Polynomial.X ^ 12,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · compute_degree!
  · simp
  · compute_degree!
  · simp
  · simp [Polynomial.coeff_ofNat_mul]
  · simp only [Polynomial.derivative_mul, Polynomial.derivative_X_pow, Polynomial.derivative_ofNat,
      zero_mul, zero_add, map_natCast]
    push_cast
    ring
  · simp

end BranchC
