/-
  W1-O5 — Theorem R campaign, leg W1-O5 (2026-11-22).
  Standalone formalization (fresh code; imports Mathlib only, no repo modules).

  (b) Binary-form lemma (paper `lem:binary`, corrected with `g ≠ 0`):
      homogeneous f, g ∈ K[x,y] of the same degree d ≥ 1, char 0, g ≠ 0,
      f_x g_y - f_y g_x = 0  ⇒  f = r • g.
  (a) E₁ chart step (paper `lem:e1`, Step 1) as a polynomial identity
      (design note `o5_design.md` §2): the section `e1Section S d`
      = (s₁ t₁)^d · S(1/(s₁t₁), 1/t₁) ∈ K[t₁][s₁].
-/
import Mathlib

namespace O5

variable {K : Type*} [Field K] [CharZero K]

/-! ## One-variable Wronskian lemma (re-proved fresh) -/

section Wronskian

open Polynomial

/-- Top coefficient of `F * G'` at `m + n - 1`. -/
lemma coeff_mul_derivative_top (F G : Polynomial K) (hmn : 1 ≤ F.natDegree + G.natDegree) :
    (F * derivative G).coeff (F.natDegree + G.natDegree - 1)
      = F.leadingCoeff * G.leadingCoeff * (G.natDegree : K) := by
  rcases Nat.eq_zero_or_pos G.natDegree with h0 | hpos
  · rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
    simp [h0]
  · have hdeg : (derivative G).natDegree ≤ G.natDegree - 1 := natDegree_derivative_le G
    have hidx : F.natDegree + G.natDegree - 1 = F.natDegree + (G.natDegree - 1) := by omega
    rw [hidx, coeff_mul_add_eq_of_natDegree_le le_rfl hdeg, coeff_derivative]
    have : G.natDegree - 1 + 1 = G.natDegree := by omega
    rw [this]
    simp only [leadingCoeff]
    have hc : ((G.natDegree - 1 : ℕ) : K) + 1 = (G.natDegree : K) := by
      rw [← Nat.cast_succ, Nat.succ_eq_add_one, this]
    rw [hc]; ring

/-- Top coefficient of `F' * G` at `m + n - 1`. -/
lemma coeff_derivative_mul_top (F G : Polynomial K) (hmn : 1 ≤ F.natDegree + G.natDegree) :
    (derivative F * G).coeff (F.natDegree + G.natDegree - 1)
      = F.leadingCoeff * G.leadingCoeff * (F.natDegree : K) := by
  have h := coeff_mul_derivative_top G F (by omega)
  rw [mul_comm (derivative F) G, add_comm F.natDegree G.natDegree, h]
  ring

lemma natDegree_eq_of_wronskian {F G : Polynomial K} (hF : F ≠ 0) (hG : G ≠ 0)
    (hW : F * derivative G = derivative F * G) : F.natDegree = G.natDegree := by
  by_contra hne
  have hmn : 1 ≤ F.natDegree + G.natDegree := by omega
  have h1 := coeff_mul_derivative_top F G hmn
  have h2 := coeff_derivative_mul_top F G hmn
  rw [hW, h2] at h1
  have ha : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hF
  have hb : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hG
  have hcast : (F.natDegree : K) ≠ (G.natDegree : K) := by
    exact_mod_cast hne
  apply hcast
  have hab : F.leadingCoeff * G.leadingCoeff ≠ 0 := mul_ne_zero ha hb
  exact mul_left_cancel₀ hab h1

/-- **One-variable Wronskian lemma.** Over a field of characteristic zero,
if `G ≠ 0` and `F G' = F' G` then `F = C r * G` for some `r`. -/
theorem eq_C_mul_of_wronskian {F G : Polynomial K} (hG : G ≠ 0)
    (hW : F * derivative G = derivative F * G) : ∃ r : K, F = C r * G := by
  by_cases hF : F = 0
  · exact ⟨0, by simp [hF]⟩
  have hdeg := natDegree_eq_of_wronskian hF hG hW
  set r : K := F.leadingCoeff / G.leadingCoeff with hr
  refine ⟨r, ?_⟩
  by_contra hne
  set H : Polynomial K := F - C r * G with hH
  have hH0 : H ≠ 0 := sub_ne_zero.mpr hne
  have hWH : H * derivative G = derivative H * G := by
    simp only [hH, derivative_sub, derivative_C_mul]
    linear_combination hW
  have hdH := natDegree_eq_of_wronskian hH0 hG hWH
  have hb : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hG
  have hcoef : H.coeff G.natDegree = 0 := by
    simp only [hH, coeff_sub, coeff_C_mul]
    have e1 : F.coeff G.natDegree = F.leadingCoeff := by rw [← hdeg]; rfl
    have e2 : G.coeff G.natDegree = G.leadingCoeff := rfl
    rw [e1, e2, hr, div_mul_cancel₀ _ hb, sub_self]
  apply hH0
  have : H.leadingCoeff = 0 := by
    simp only [leadingCoeff, hdH]; exact hcoef
  exact leadingCoeff_eq_zero.mp this

end Wronskian

open MvPolynomial

/-- The Jacobian bracket `[f,g] = f_x g_y - f_y g_x` (`X 0 = x`, `X 1 = y`). -/
noncomputable def jacobian (f g : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  pderiv 0 f * pderiv 1 g - pderiv 1 f * pderiv 0 g

/-! ## (b) The binary-form lemma -/

/-- Dehomogenization at `y = 1`: `f(x,y) ↦ f(X,1)`. -/
noncomputable def dehomog (f : MvPolynomial (Fin 2) K) : Polynomial K :=
  aeval (![Polynomial.X, 1] : Fin 2 → Polynomial K) f

lemma dehomog_X0 : dehomog (X 0 : MvPolynomial (Fin 2) K) = Polynomial.X := by
  simp [dehomog]

lemma dehomog_X1 : dehomog (X 1 : MvPolynomial (Fin 2) K) = 1 := by
  simp [dehomog]

lemma dehomog_C (a : K) : dehomog (C a : MvPolynomial (Fin 2) K) = Polynomial.C a := by
  simp [dehomog, Polynomial.algebraMap_eq]

lemma dehomog_zero : dehomog (0 : MvPolynomial (Fin 2) K) = 0 := by simp [dehomog]

lemma dehomog_one : dehomog (1 : MvPolynomial (Fin 2) K) = 1 := by simp [dehomog]

lemma dehomog_add (f g : MvPolynomial (Fin 2) K) :
    dehomog (f + g) = dehomog f + dehomog g := by simp [dehomog]

lemma dehomog_sub (f g : MvPolynomial (Fin 2) K) :
    dehomog (f - g) = dehomog f - dehomog g := by simp [dehomog]

lemma dehomog_mul (f g : MvPolynomial (Fin 2) K) :
    dehomog (f * g) = dehomog f * dehomog g := by simp [dehomog]

/-- Derivative commutes with dehomogenization (in `x`). -/
theorem derivative_dehomog (f : MvPolynomial (Fin 2) K) :
    Polynomial.derivative (dehomog f) = dehomog (pderiv 0 f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [dehomog_C, dehomog_zero]
  | add p q hp hq =>
    rw [dehomog_add, Polynomial.derivative_add, hp, hq, map_add, dehomog_add]
  | mul_X p n hp =>
    rw [dehomog_mul, Polynomial.derivative_mul, hp, Derivation.leibniz, smul_eq_mul,
      smul_eq_mul, dehomog_add, dehomog_mul, dehomog_mul]
    fin_cases n
    · simp [dehomog_X0, pderiv_X, dehomog_one]
      ring
    · simp [dehomog_X1, pderiv_X, dehomog_zero]

/-- Euler's relation at `y = 1`. -/
theorem dehomog_pderiv_one {f : MvPolynomial (Fin 2) K} {d : ℕ} (hf : f.IsHomogeneous d) :
    dehomog (pderiv 1 f)
      = (d : Polynomial K) * dehomog f - Polynomial.X * Polynomial.derivative (dehomog f) := by
  have hE := hf.sum_X_mul_pderiv
  have h2 := congrArg dehomog hE
  rw [Fin.sum_univ_two, dehomog_add, dehomog_mul, dehomog_mul, dehomog_X0, dehomog_X1,
    nsmul_eq_mul, dehomog_mul, ← derivative_dehomog] at h2
  have hd : dehomog (d : MvPolynomial (Fin 2) K) = (d : Polynomial K) := by
    simp [dehomog]
  rw [hd] at h2
  linear_combination h2

/-- Exponents of `Fin 2`: total degree. -/
lemma degree_fin2 (t : Fin 2 →₀ ℕ) : t.degree = t 0 + t 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

lemma fin2_ext {s t : Fin 2 →₀ ℕ} (h0 : s 0 = t 0) (h1 : s 1 = t 1) : s = t := by
  ext i; fin_cases i <;> simpa

/-- Homogeneous support: `t 0 + t 1 = d`. -/
lemma homog_support {f : MvPolynomial (Fin 2) K} {d : ℕ} (hf : f.IsHomogeneous d)
    {t : Fin 2 →₀ ℕ} (ht : f.coeff t ≠ 0) : t 0 + t 1 = d := by
  by_contra h
  exact ht (hf.coeff_eq_zero (d := t) (by rw [degree_fin2]; exact h))

/-- Coefficient dictionary for `dehomog`. -/
lemma coeff_dehomog (f : MvPolynomial (Fin 2) K) (i : ℕ) :
    (dehomog f).coeff i = ∑ t ∈ f.support, if i = t 0 then f.coeff t else 0 := by
  unfold dehomog
  rw [aeval_def, eval₂_eq', Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Fin.prod_univ_two]
  simp [Polynomial.algebraMap_eq, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]

/-- A homogeneous form with vanishing dehomogenization is zero. -/
theorem eq_zero_of_dehomog_eq_zero {h : MvPolynomial (Fin 2) K} {d : ℕ}
    (hh : h.IsHomogeneous d) (h0 : dehomog h = 0) : h = 0 := by
  by_contra hne
  obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp hne
  have hc := coeff_dehomog h (s 0)
  rw [h0, Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single s] at hc
  · simp at hc; exact hs hc.symm
  · intro t ht hts
    rw [mem_support_iff] at ht
    split_ifs with h1
    · exfalso; apply hts
      have e1 := homog_support hh ht
      have e2 := homog_support hh hs
      exact fin2_ext h1.symm (by omega)
    · rfl
  · intro hns
    exact absurd (mem_support_iff.mpr hs) hns

/-- **The binary-form lemma** (paper `lem:binary`, corrected with `g ≠ 0`). -/
theorem binary_form_proportional {f g : MvPolynomial (Fin 2) K} {d : ℕ}
    (hd : 1 ≤ d) (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous d)
    (hg0 : g ≠ 0) (hbr : jacobian f g = 0) :
    ∃ r : K, f = C r * g := by
  have hG : dehomog g ≠ 0 := fun h => hg0 (eq_zero_of_dehomog_eq_zero hg h)
  have hJ := congrArg dehomog hbr
  unfold jacobian at hJ
  rw [dehomog_sub, dehomog_mul, dehomog_mul, ← derivative_dehomog, ← derivative_dehomog,
    dehomog_pderiv_one hf, dehomog_pderiv_one hg] at hJ
  have hJ0 : dehomog (0 : MvPolynomial (Fin 2) K) = 0 := by simp [dehomog]
  rw [hJ0] at hJ
  have hdne : (d : Polynomial K) ≠ 0 := by
    have : (d : K) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    intro h; apply this
    have := congrArg (fun p => Polynomial.coeff p 0) h
    simpa using this
  have hW : dehomog f * Polynomial.derivative (dehomog g)
      = Polynomial.derivative (dehomog f) * dehomog g := by
    have key : (d : Polynomial K) * (Polynomial.derivative (dehomog f) * dehomog g
        - dehomog f * Polynomial.derivative (dehomog g)) = 0 := by
      linear_combination hJ
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hdne
    · linear_combination -h
  obtain ⟨r, hr⟩ := eq_C_mul_of_wronskian hG hW
  refine ⟨r, ?_⟩
  have hhom : (f - C r * g).IsHomogeneous d := by
    have := (hg.C_mul r)
    exact hf.sub this
  have hz : dehomog (f - C r * g) = 0 := by
    rw [dehomog_sub, dehomog_mul, dehomog_C, hr, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_dehomog_eq_zero hhom hz)

/-- **The paper's `lem:binary` is false without `g ≠ 0`**: `f = x`, `g = 0` over `ℚ`. -/
theorem binary_form_needs_g_ne_zero :
    ∃ f g : MvPolynomial (Fin 2) ℚ, f.IsHomogeneous 1 ∧ g.IsHomogeneous 1 ∧
      jacobian f g = 0 ∧ ¬ ∃ r : ℚ, f = C r * g := by
  refine ⟨X 0, 0, isHomogeneous_X ℚ 0, isHomogeneous_zero _ _ _, by simp [jacobian], ?_⟩
  rintro ⟨r, hr⟩
  simp at hr

/-! ## (a) The E₁ chart step -/

/-- The E₁ section `(s₁t₁)^d · S(1/(s₁t₁), 1/t₁)` as an element of `K[t₁][s₁]`:
the monomial `x^i y^j` with coefficient `a` contributes `a · s₁^{d-i} · t₁^{d-i-j}`.
(Chart of check 5: blow-up of `[1:0:0]`, `s = y/x`, `t = 1/x`, `s = s₁`, `t = s₁t₁`.) -/
noncomputable def e1Section (S : MvPolynomial (Fin 2) K) (d : ℕ) :
    Polynomial (Polynomial K) :=
  ∑ e ∈ S.support, Polynomial.monomial (d - e 0)
    (Polynomial.C (S.coeff e) * Polynomial.X ^ (d - e 0 - e 1))

/-- Double-coefficient formula for the section. -/
lemma coeff_coeff_e1Section (S : MvPolynomial (Fin 2) K) (d k m : ℕ) :
    ((e1Section S d).coeff k).coeff m
      = ∑ e ∈ S.support, if d - e 0 = k ∧ d - e 0 - e 1 = m then S.coeff e else 0 := by
  unfold e1Section
  rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Polynomial.coeff_monomial]
  by_cases h1 : d - e 0 = k
  · simp [h1, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, eq_comm]
  · simp [h1]

lemma support_sum_le {S : MvPolynomial (Fin 2) K} {d : ℕ} (hS : S.totalDegree ≤ d)
    {e : Fin 2 →₀ ℕ} (he : e ∈ S.support) : e 0 + e 1 ≤ d := by
  have h := MvPolynomial.le_totalDegree he
  rw [Finsupp.sum_fintype _ _ (by intro; rfl), Fin.sum_univ_two] at h
  omega

/-- **Vanishing below the leading power** `s₁^{d-n}`, `n = deg_x S`. -/
theorem e1Section_coeff_eq_zero_of_lt (S : MvPolynomial (Fin 2) K) (d k : ℕ)
    (hk : k < d - S.degreeOf 0) : (e1Section S d).coeff k = 0 := by
  ext m
  rw [coeff_coeff_e1Section, Polynomial.coeff_zero]
  refine Finset.sum_eq_zero (fun e he => ?_)
  have hle := MvPolynomial.monomial_le_degreeOf 0 he
  rw [if_neg]
  omega

/-- **The restriction formula, coefficient form** (corrected check-5 form):
the `s₁^{d-n}`-coefficient of the section is `t₁^{d-n} A(1/t₁)`, where
`A(y) = ∑_j c_{n j} y^j` is the `xⁿ`-coefficient of `S`; i.e. its
`t₁^m`-coefficient is `c_{n, d-n-m}` for `m ≤ d - n`, and `0` for `m > d - n`. -/
theorem e1Section_coeff_top_coeff (S : MvPolynomial (Fin 2) K) (d m : ℕ)
    (hS : S.totalDegree ≤ d) :
    ((e1Section S d).coeff (d - S.degreeOf 0)).coeff m
      = if m ≤ d - S.degreeOf 0 then
          S.coeff (Finsupp.single 0 (S.degreeOf 0)
            + Finsupp.single 1 (d - S.degreeOf 0 - m))
        else 0 := by
  set n := S.degreeOf 0 with hn
  have hnd : n ≤ d := le_trans (degreeOf_le_totalDegree S 0) hS
  rw [coeff_coeff_e1Section]
  split_ifs with hm
  · rw [Finset.sum_eq_single (Finsupp.single 0 n + Finsupp.single 1 (d - n - m))]
    · rw [if_pos]
      simp
      omega
    · intro e he hne
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply hne
      have hle := MvPolynomial.monomial_le_degreeOf 0 he
      have hsum := support_sum_le hS he
      apply fin2_ext
      · simp; omega
      · simp; omega
    · intro hns
      rw [MvPolynomial.notMem_support_iff.mp hns]
      simp
  · refine Finset.sum_eq_zero (fun e he => ?_)
    rw [if_neg]
    have hle := MvPolynomial.monomial_le_degreeOf 0 he
    omega

/-- **The restriction formula, sum form.** -/
theorem e1Section_coeff_top (S : MvPolynomial (Fin 2) K) (d : ℕ) (hS : S.totalDegree ≤ d) :
    (e1Section S d).coeff (d - S.degreeOf 0) =
      ∑ j ∈ Finset.range (d - S.degreeOf 0 + 1),
        Polynomial.C (S.coeff (Finsupp.single 0 (S.degreeOf 0) + Finsupp.single 1 j)) *
          Polynomial.X ^ (d - S.degreeOf 0 - j) := by
  set n := S.degreeOf 0 with hn
  ext m
  rw [e1Section_coeff_top_coeff S d m hS, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs with hm
  · rw [Finset.sum_eq_single (d - n - m)]
    · have : m = d - n - (d - n - m) := by omega
      rw [if_pos this, mul_one]
    · intro j hj hjne
      have : m ≠ d - n - j := by simp at hj; omega
      simp [this]
    · intro h; simp at h <;> omega
  · refine (Finset.sum_eq_zero (fun j hj => ?_)).symm
    have : m ≠ d - n - j := by simp at hj; omega
    simp [this]

/-- **Nonzero iff some `xⁿ`-coefficient is nonzero.** -/
theorem e1Section_top_ne_zero_iff (S : MvPolynomial (Fin 2) K) (d : ℕ)
    (hS : S.totalDegree ≤ d) :
    (e1Section S d).coeff (d - S.degreeOf 0) ≠ 0 ↔
      ∃ j ≤ d - S.degreeOf 0,
        S.coeff (Finsupp.single 0 (S.degreeOf 0) + Finsupp.single 1 j) ≠ 0 := by
  set n := S.degreeOf 0 with hn
  constructor
  · intro h
    obtain ⟨m, hm⟩ : ∃ m, ((e1Section S d).coeff (d - n)).coeff m ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact h (Polynomial.ext (by simpa using hall))
    rw [e1Section_coeff_top_coeff S d m hS] at hm
    split_ifs at hm with hle
    · exact ⟨d - n - m, by omega, hm⟩
    · exact absurd rfl hm
  · rintro ⟨j, hj, hc⟩ h0
    have := e1Section_coeff_top_coeff S d (d - n - j) hS
    rw [h0, Polynomial.coeff_zero, if_pos (by omega)] at this
    have hjj : d - n - (d - n - j) = j := by omega
    rw [hjj] at this
    exact hc this.symm

/-- For `S ≠ 0` the section's lowest `s₁`-power is exactly `d - n`
(i.e. `ν_{E₁}` sees exactly the `x`-degree). -/
theorem e1Section_top_ne_zero (S : MvPolynomial (Fin 2) K) (d : ℕ)
    (hS : S.totalDegree ≤ d) (hS0 : S ≠ 0) :
    (e1Section S d).coeff (d - S.degreeOf 0) ≠ 0 := by
  rw [e1Section_top_ne_zero_iff S d hS]
  obtain ⟨e, he, hee⟩ := Finset.exists_mem_eq_sup S.support
    (Finset.nonempty_iff_ne_empty.mpr (fun h => hS0 (support_eq_empty.mp h))) (fun m => m 0)
  have hn : S.degreeOf 0 = e 0 := by rw [MvPolynomial.degreeOf_eq_sup]; exact hee
  have hsum := support_sum_le hS he
  refine ⟨e 1, by omega, ?_⟩
  have : Finsupp.single 0 (S.degreeOf 0) + Finsupp.single 1 (e 1) = e := by
    apply fin2_ext <;> simp [hn]
  rw [this]
  exact mem_support_iff.mp he

/-- **Differing `x`-degrees** (paper: restriction `∞` resp. `0`), as an order comparison. -/
theorem e1_restriction_degenerate {P Q : MvPolynomial (Fin 2) K} (d : ℕ)
    (h : Q.degreeOf 0 < P.degreeOf 0) (hd : P.degreeOf 0 ≤ d) :
    (e1Section Q d).coeff (d - P.degreeOf 0) = 0 :=
  e1Section_coeff_eq_zero_of_lt Q d _ (by omega)

/-- **The ratio corollary.** Same `x`-degree `n`, common normalization `d`
(any `d ≥` both total degrees), coefficient-wise proportional `xⁿ`-coefficients
⇒ proportional leading coefficients. -/
theorem e1_restriction_proportional {P Q : MvPolynomial (Fin 2) K} (d : ℕ)
    (hP : P.totalDegree ≤ d) (hQ : Q.totalDegree ≤ d)
    (hn : P.degreeOf 0 = Q.degreeOf 0) (r : K)
    (hcoeff : ∀ j, P.coeff (Finsupp.single 0 (P.degreeOf 0) + Finsupp.single 1 j)
      = r * Q.coeff (Finsupp.single 0 (Q.degreeOf 0) + Finsupp.single 1 j)) :
    (e1Section P d).coeff (d - P.degreeOf 0)
      = Polynomial.C r * (e1Section Q d).coeff (d - Q.degreeOf 0) := by
  ext m
  rw [Polynomial.coeff_C_mul, e1Section_coeff_top_coeff P d m hP,
    e1Section_coeff_top_coeff Q d m hQ, hn]
  split_ifs
  · rw [← hn, hcoeff, hn]
  · simp

/-- **Change of normalization.** Normalizing by `d + k` instead of `d` multiplies the
section by `(s₁t₁)^k`. This is the source of the `t₁^{d-n}` factor discrepancy:
it cancels against `(s₁t₁)^{d_Q-d_P}` when `P/Q` is written over a common
normalization, so the restriction `P/Q|_{E₁} = A(1/t₁)/D(1/t₁)` needs no
Keller input. -/
theorem e1Section_shift (S : MvPolynomial (Fin 2) K) (d k : ℕ) (hS : S.totalDegree ≤ d) :
    e1Section S (d + k) = Polynomial.monomial k (Polynomial.X ^ k) * e1Section S d := by
  unfold e1Section
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have hsum := support_sum_le hS he
  rw [Polynomial.monomial_mul_monomial]
  have h1 : d + k - e 0 = k + (d - e 0) := by omega
  have h2 : d + k - e 0 - e 1 = k + (d - e 0 - e 1) := by omega
  rw [h2, h1, pow_add]
  ring

/-! ## Axiom audit -/
#print axioms eq_C_mul_of_wronskian
#print axioms derivative_dehomog
#print axioms dehomog_pderiv_one
#print axioms eq_zero_of_dehomog_eq_zero
#print axioms binary_form_proportional
#print axioms binary_form_needs_g_ne_zero
#print axioms coeff_coeff_e1Section
#print axioms e1Section_coeff_eq_zero_of_lt
#print axioms e1Section_coeff_top_coeff
#print axioms e1Section_coeff_top
#print axioms e1Section_top_ne_zero_iff
#print axioms e1Section_top_ne_zero
#print axioms e1_restriction_degenerate
#print axioms e1_restriction_proportional
#print axioms e1Section_shift

end O5
