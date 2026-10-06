import Jacobian.B26Count

/-!
# Irreducibility of the eliminants `T₃` and `T₅` over `ℚ`

`T₃ = 3X³ - 32` and `T₅ = 9X¹⁰ + 37200X⁵ + 95051008` (`T3poly`, `T5poly` in `Jacobian/B26Count.lean`) are
irreducible over `ℚ` (`T3poly_irreducible`, `T5poly_irreducible`).

No other result of the package uses these two theorems: the classifications (`m3_chart_iff`, `m5_chart_iff`) and the
solution counts (`m3_chart_card`, `m5_chart_card`) do not need them. Outside Lean, the irreducibility is checked by
factorization (`scripts/e5_exact_counts_m35.py`, `scripts/a816_certificate/b26_check.py`).

**`T₃`.** A cubic over a field with no root is irreducible
(`Polynomial.irreducible_of_degree_le_three_of_not_isRoot`). A rational root `q` would give `q³ = 32/3`. But
`v₃(32/3) = -1` is not a multiple of `3`.

**`T₅`.** Write `T₅ = F(X⁵)` with `F = 9Y² + 37200Y + 95051008` (`T5quad`).
1. `F = (3Y + 6200)² + 56611008` has no rational root, so it is irreducible.
2. Let `K = ℚ(u)` with `F(u) = 0` (`T5Base = AdjoinRoot T5quad`). The norm `N_{K/ℚ}(u)` is `95051008/9`. Its
   `3`-adic valuation is `-2`, since `95051008 = 2⁸·13⁵` is prime to `3`. The norm is multiplicative and `-2` is not
   a multiple of `5`, so `u` is not a fifth power in `K`.
3. Hence `X⁵ - u` is irreducible over `K` (`X_pow_sub_C_irreducible_of_prime`, `5` prime). Let `L = K(θ)` with
   `θ⁵ = u` (`T5Top`, `T5root`). Then `[L : ℚ] = [K : ℚ]·[L : K] = 2·5 = 10`.
4. `u = θ⁵ ∈ ℚ[θ]`, so `ℚ[θ]` contains the image of `K`; it also contains `θ`, and `K[θ] = L`. So `ℚ[θ] = L`, and
   the minimal polynomial of `θ` over `ℚ` has degree `10`.
5. `T₅(θ) = F(θ⁵) = F(u) = 0`, so this minimal polynomial divides `T₅`. Both have degree `10`, so `T₅` is a
   nonzero constant times the minimal polynomial; hence `T₅` is irreducible.

Note on instances: `T5Base` is a number field, so instance search gives it the `ℚ`-algebra structure
`DivisionRing.toRatAlgebra`; the `AdjoinRoot` lemmas are stated with `AdjoinRoot.instAlgebra`. The two are
definitionally equal; `aeval_root_T5quad` and `norm_root_T5quad` bridge them by term-mode `Eq.trans`.
-/

namespace BranchAb.TopLayerSmall

open Polynomial

/-! ### `3`-adic valuations -/

lemma padicValRat_three_self : padicValRat 3 (3 : ℚ) = 1 := by
  have e : ((3 : ℕ) : ℚ) = (3 : ℚ) := by norm_num
  rw [← e, padicValRat.self (by norm_num)]

/-- `v₃(95051008 / 9) = -2`. -/
lemma padicValRat_three_T5norm : padicValRat 3 ((95051008 : ℚ) / 9) = -2 := by
  rw [padicValRat.div (by norm_num) (by norm_num)]
  have h2 : padicValRat 3 (95051008 : ℚ) = 0 := by
    have e : ((95051008 : ℕ) : ℚ) = (95051008 : ℚ) := by norm_num
    rw [← e, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by norm_num)]; rfl
  have h3 : padicValRat 3 (9 : ℚ) = 2 := by
    have e : (9 : ℚ) = (3 : ℚ) ^ 2 := by norm_num
    rw [e, padicValRat.pow, padicValRat_three_self]; norm_num
  rw [h2, h3]; norm_num

/-- `95051008 / 9` is not the fifth power of a rational number. -/
lemma rat_pow_five_ne_T5norm (q : ℚ) : q ^ 5 ≠ 95051008 / 9 := by
  intro h
  have h1 : padicValRat 3 (q ^ 5) = padicValRat 3 ((95051008 : ℚ) / 9) := by rw [h]
  rw [padicValRat.pow, padicValRat_three_T5norm] at h1
  omega

/-- `32 / 3` is not the cube of a rational number. -/
lemma rat_pow_three_ne_T3root (q : ℚ) : q ^ 3 ≠ 32 / 3 := by
  intro h
  have h1 : padicValRat 3 (q ^ 3) = padicValRat 3 ((32 : ℚ) / 3) := by rw [h]
  rw [padicValRat.pow, padicValRat.div (by norm_num) (by norm_num)] at h1
  have h2 : padicValRat 3 (32 : ℚ) = 0 := by
    have e : ((32 : ℕ) : ℚ) = (32 : ℚ) := by norm_num
    rw [← e, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by norm_num)]; rfl
  rw [h2, padicValRat_three_self] at h1
  omega

/-! ### `T₃` -/

/-- **`T₃ = 3X³ - 32` is irreducible over `ℚ`.** -/
theorem T3poly_irreducible : Irreducible T3poly := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [T3poly_natDegree]; decide
  · intro x hx
    simp only [T3poly, IsRoot, eval_sub, eval_mul, eval_C, eval_pow, eval_X] at hx
    exact rat_pow_three_ne_T3root x (by linear_combination hx / 3)

/-! ### `T₅`: the quadratic `F` and its root field `K = ℚ(u)` -/

/-- `F = 9Y² + 37200Y + 95051008`, so that `T₅ = F(X⁵)`. -/
noncomputable def T5quad : ℚ[X] := C 9 * X ^ 2 + C 37200 * X + C 95051008

lemma T5quad_natDegree : T5quad.natDegree = 2 := by unfold T5quad; compute_degree!

/-- `F` has no rational root: `F(Y) = (3Y + 6200)² + 56611008 > 0`. -/
lemma T5quad_irreducible : Irreducible T5quad := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [T5quad_natDegree]; decide
  · intro x hx
    simp only [T5quad, IsRoot, eval_add, eval_mul, eval_C, eval_pow, eval_X] at hx
    nlinarith [sq_nonneg (3 * x + 6200)]

lemma T5quad_ne_zero : T5quad ≠ 0 := T5quad_irreducible.ne_zero

instance T5quad_fact : Fact (Irreducible T5quad) := ⟨T5quad_irreducible⟩

lemma T5quad_leadingCoeff : T5quad.leadingCoeff = 9 := by
  rw [leadingCoeff, T5quad_natDegree]; simp [T5quad]

/-- `K = ℚ(u)` with `F(u) = 0`, a quadratic number field. -/
noncomputable abbrev T5Base : Type := AdjoinRoot T5quad

/-- `N_{K/ℚ}(u) = 95051008 / 9`. -/
lemma norm_root_T5quad : Algebra.norm ℚ (AdjoinRoot.root T5quad) = 95051008 / 9 := by
  have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (AdjoinRoot.powerBasis T5quad_ne_zero)
  rw [AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim, AdjoinRoot.minpoly_root T5quad_ne_zero,
    T5quad_natDegree, T5quad_leadingCoeff] at h
  refine h.trans ?_
  simp [T5quad]
  norm_num

/-- `u` is not a fifth power in `K`. -/
lemma root_T5quad_ne_pow_five (b : T5Base) : b ^ 5 ≠ AdjoinRoot.root T5quad := by
  intro hb
  have h := congrArg (Algebra.norm ℚ) hb
  rw [map_pow, norm_root_T5quad] at h
  exact rat_pow_five_ne_T5norm _ h

/-! ### `T₅`: the Kummer extension `L = K(θ)`, `θ⁵ = u` -/

/-- `X⁵ - u` over `K`. -/
noncomputable def T5kummer : T5Base[X] := X ^ 5 - C (AdjoinRoot.root T5quad)

lemma T5kummer_irreducible : Irreducible T5kummer :=
  X_pow_sub_C_irreducible_of_prime (by norm_num) root_T5quad_ne_pow_five

lemma T5kummer_ne_zero : T5kummer ≠ 0 := T5kummer_irreducible.ne_zero

instance T5kummer_fact : Fact (Irreducible T5kummer) := ⟨T5kummer_irreducible⟩

/-- `L = K(θ)` with `θ⁵ = u`. -/
noncomputable abbrev T5Top : Type := AdjoinRoot T5kummer

/-- `θ`, a root of `T₅` that generates `L` over `ℚ`. -/
noncomputable def T5root : T5Top := AdjoinRoot.root T5kummer

lemma T5root_pow_five : T5root ^ 5 = algebraMap T5Base T5Top (AdjoinRoot.root T5quad) :=
  root_X_pow_sub_C_pow 5 (AdjoinRoot.root T5quad)

/-- `F(u) = 0`, for the `ℚ`-algebra structure that instance search finds on `K`. -/
lemma aeval_root_T5quad : aeval (AdjoinRoot.root T5quad) T5quad = 0 :=
  (AdjoinRoot.aeval_eq T5quad).trans AdjoinRoot.mk_self

/-- `T₅(θ) = F(θ⁵) = F(u) = 0`. -/
lemma aeval_T5root : aeval T5root T5poly = 0 := by
  have h1 : aeval T5root T5poly = aeval (T5root ^ 5) T5quad := by
    simp only [T5poly, T5quad, map_add, map_mul, aeval_C, map_pow, aeval_X]
    ring
  rw [h1, T5root_pow_five, aeval_algebraMap_apply, aeval_root_T5quad, map_zero]

instance T5Top_finite_T5Base : Module.Finite T5Base T5Top :=
  (AdjoinRoot.powerBasis T5kummer_ne_zero).finite

instance T5Top_finite : Module.Finite ℚ T5Top := Module.Finite.trans T5Base T5Top

lemma finrank_T5Base : Module.finrank ℚ T5Base = 2 := by
  rw [(AdjoinRoot.powerBasis T5quad_ne_zero).finrank, AdjoinRoot.powerBasis_dim, T5quad_natDegree]

lemma finrank_T5Top_T5Base : Module.finrank T5Base T5Top = 5 := by
  rw [(AdjoinRoot.powerBasis T5kummer_ne_zero).finrank, AdjoinRoot.powerBasis_dim, T5kummer,
    natDegree_X_pow_sub_C]

/-- `[L : ℚ] = 10`. -/
lemma finrank_T5Top : Module.finrank ℚ T5Top = 10 := by
  rw [← Module.finrank_mul_finrank ℚ T5Base T5Top, finrank_T5Base, finrank_T5Top_T5Base]

/-- The image of `K` lies in `ℚ[θ]`: an element `q(u)` of `K` maps to `q(θ⁵)`. -/
lemma algebraMap_T5Base_mem (a : T5Base) : algebraMap T5Base T5Top a ∈ Algebra.adjoin ℚ {T5root} := by
  induction a using AdjoinRoot.induction_on with
  | ih q =>
    rw [← AdjoinRoot.aeval_eq, ← aeval_algebraMap_apply, ← T5root_pow_five]
    have h : aeval (T5root ^ 5) q = aeval T5root (q.comp (X ^ 5)) := by
      rw [aeval_comp, map_pow, aeval_X]
    rw [h]
    exact Polynomial.aeval_mem_adjoin_singleton ℚ T5root

/-- `ℚ[θ] = L`. -/
lemma adjoin_T5root : Algebra.adjoin ℚ {T5root} = ⊤ := by
  -- `ℚ[θ]` contains the image of `K`, so it is a `K`-subalgebra; it contains `θ`, and `K[θ] = L`.
  let S : Subalgebra T5Base T5Top :=
    { (Algebra.adjoin ℚ {T5root}).toSubsemiring with algebraMap_mem' := algebraMap_T5Base_mem }
  have htop : Algebra.adjoin T5Base {T5root} = ⊤ := AdjoinRoot.adjoinRoot_eq_top
  have hθ : T5root ∈ S := Algebra.self_mem_adjoin_singleton ℚ T5root
  have hle : Algebra.adjoin T5Base {T5root} ≤ S := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hθ)
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Algebra.adjoin T5Base {T5root} := by rw [htop]; exact Algebra.mem_top
  exact hle hx

lemma T5root_isIntegral : IsIntegral ℚ T5root := IsIntegral.of_finite ℚ T5root

/-- The minimal polynomial of `θ` over `ℚ` has degree `10`. -/
lemma minpoly_T5root_natDegree : (minpoly ℚ T5root).natDegree = 10 := by
  rw [← finrank_T5Top]
  exact (Field.primitive_element_iff_minpoly_natDegree_eq ℚ T5root).mp
    (IntermediateField.adjoin_eq_top_of_algebra ℚ {T5root} adjoin_T5root)

/-- **`T₅ = 9X¹⁰ + 37200X⁵ + 95051008` is irreducible over `ℚ`.** -/
theorem T5poly_irreducible : Irreducible T5poly := by
  have hdvd : minpoly ℚ T5root ∣ T5poly := minpoly.dvd ℚ T5root aeval_T5root
  have heq := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic T5root_isIntegral) hdvd
    (by rw [T5poly_natDegree, minpoly_T5root_natDegree])
  have hunit : IsUnit (C T5poly.leadingCoeff) :=
    isUnit_C.mpr (leadingCoeff_ne_zero.mpr T5poly_ne_zero).isUnit
  rw [heq, irreducible_isUnit_mul hunit]
  exact minpoly.irreducible T5root_isIntegral

end BranchAb.TopLayerSmall
