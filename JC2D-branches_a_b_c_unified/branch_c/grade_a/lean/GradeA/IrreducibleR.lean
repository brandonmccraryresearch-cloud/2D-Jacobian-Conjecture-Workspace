import GradeA.R67Data

/-!
# `R = X⁵ − X⁴ + 3X³ + 3X² + 26` is irreducible over `ℚ`

Branch (c), premise H3 of `branch_c/rank_lemma_check/README.md` (until now grade B: FLINT factorization, and
irreducibility modulo 67 checked in Python). Here it is proved in Lean, with no `sorry`.

1. `R mod 67` has no root in `𝔽₆₇` and no monic quadratic factor: `R67Data.lean` decides both on integers
   (`R_no_root_int`, `rem_not_both_zero`); they are transferred to `𝔽₆₇[X]` here (`R67_no_root`, `R67_no_quad`).
2. A monic quintic over a field with no monic factor of degree 1 or 2 is irreducible
   (`Polynomial.Monic.irreducible_iff_lt_natDegree_lt`: only factors of degree ≤ ⌊5/2⌋ = 2 need checking).
3. `R` is monic over `ℤ` and irreducible mod 67, so it is irreducible over `ℤ`
   (`Polynomial.Monic.irreducible_of_irreducible_map`), and over `ℚ` by Gauss's lemma
   (`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`).
4. Consequences used by the transfer (`Transfer.lean`): for a root `w` of `R` in any field of characteristic 0, the
   minimal polynomial of `w` over `ℚ` is `R`, so `R` divides every rational polynomial that vanishes at `w`.

The draft `a3_irreducibility_transfer/IrreducibleR.lean` of the branch `caic/branch-c-cleanup` (2026-10-11) has
the same computational part; its final case analysis was left as `sorry`. That case analysis is step 2 here.
-/

open Polynomial

namespace BranchC.GradeA

instance fact_prime_67 : Fact (Nat.Prime 67) := ⟨by norm_num⟩

/-- `R` over `ℤ`. -/
noncomputable def Rint : ℤ[X] := X ^ 5 - X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 + 26

/-- `R` over `ℚ`. -/
noncomputable def Rrat : ℚ[X] := X ^ 5 - X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 + 26

/-- `R` modulo 67. -/
noncomputable def R67 : (ZMod 67)[X] := X ^ 5 - X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 + 26

lemma Rint_map_67 : Rint.map (Int.castRingHom (ZMod 67)) = R67 := by
  simp [Rint, R67]

lemma Rint_map_rat : Rint.map (algebraMap ℤ ℚ) = Rrat := by
  simp [Rint, Rrat]

lemma Rint_monic : Rint.Monic := by
  unfold Rint; monicity!

lemma Rrat_monic : Rrat.Monic := by
  unfold Rrat; monicity!

lemma R67_natDegree : R67.natDegree = 5 := by
  unfold R67; compute_degree!

lemma R67_monic : R67.Monic := by
  unfold R67; monicity!

lemma R67_ne_one : R67 ≠ 1 := by
  intro h
  have h5 := R67_natDegree
  rw [h, natDegree_one] at h5
  exact absurd h5 (by norm_num)

/-! ### No root modulo 67 -/

lemma zmod67_eq_cast_val (x : ZMod 67) : x = (((x.val : ℕ) : ℤ) : ZMod 67) := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

lemma R67_no_root (x : ZMod 67) : ¬ R67.IsRoot x := by
  intro h
  have h0 : x ^ 5 - x ^ 4 + 3 * x ^ 3 + 3 * x ^ 2 + 26 = 0 := by
    simpa [R67, IsRoot] using h
  rw [zmod67_eq_cast_val x] at h0
  have h1 : ((((x.val : ℕ) : ℤ) ^ 5 - ((x.val : ℕ) : ℤ) ^ 4 + 3 * ((x.val : ℕ) : ℤ) ^ 3
      + 3 * ((x.val : ℕ) : ℤ) ^ 2 + 26 : ℤ) : ZMod 67) = 0 := by
    push_cast; exact h0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  exact R_no_root_int ⟨x.val, ZMod.val_lt x⟩ (by simpa using h1)

/-! ### No monic quadratic factor modulo 67 -/

/-- The quotient of `R` by `X² + aX + b`. -/
noncomputable def quot2 (a b : ZMod 67) : (ZMod 67)[X] :=
  X ^ 3 + C (-1 - a) * X ^ 2 + C (3 - b + a + a ^ 2) * X + C (3 - a * (3 - b + a + a ^ 2) - b * (-1 - a))

/-- The division identity `R = (X² + aX + b)·Q + (r₁X + r₀)`, with `r₁ = remX(a,b)` and `r₀ = remC(a,b)` cast to
`𝔽₆₇`. -/
lemma R67_div (a b : ZMod 67) :
    R67 = (X ^ 2 + C a * X + C b) * quot2 a b
      + (C ((remX (a.val : ℤ) (b.val : ℤ) : ℤ) : ZMod 67) * X + C ((remC (a.val : ℤ) (b.val : ℤ) : ℤ) : ZMod 67)) := by
  have ha : ((a.val : ℤ) : ZMod 67) = a := by
    rw [show ((a.val : ℤ) : ZMod 67) = (((a.val : ℕ) : ℤ) : ZMod 67) from rfl, ← zmod67_eq_cast_val]
  have hb : ((b.val : ℤ) : ZMod 67) = b := by
    rw [show ((b.val : ℤ) : ZMod 67) = (((b.val : ℕ) : ℤ) : ZMod 67) from rfl, ← zmod67_eq_cast_val]
  simp only [remX, remC, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, ha, hb]
  simp only [R67, quot2, map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_ofNat]
  ring

lemma R67_no_quad (a b : ZMod 67) : ¬ (X ^ 2 + C a * X + C b) ∣ R67 := by
  rintro ⟨h, hh⟩
  obtain ⟨x, hx⟩ : ∃ x : ZMod 67, ((remX (a.val : ℤ) (b.val : ℤ) : ℤ) : ZMod 67) = x := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ZMod 67, ((remC (a.val : ℤ) (b.val : ℤ) : ℤ) : ZMod 67) = y := ⟨_, rfl⟩
  have hdiv := R67_div a b
  rw [hx, hy, hh] at hdiv
  have hg_monic : (X ^ 2 + C a * X + C b : (ZMod 67)[X]).Monic := by monicity!
  have hg_deg : (X ^ 2 + C a * X + C b : (ZMod 67)[X]).natDegree = 2 := by compute_degree!
  have key : C x * X + C y = (X ^ 2 + C a * X + C b) * (h - quot2 a b) := by
    linear_combination (-1 : (ZMod 67)[X]) * hdiv
  by_cases hs : h - quot2 a b = 0
  · rw [hs, mul_zero] at key
    have hx0 : x = 0 := by
      have := congrArg (fun p => p.coeff 1) key
      simpa [coeff_C_mul_X, coeff_C] using this
    have hy0 : y = 0 := by
      have := congrArg (fun p => p.coeff 0) key
      simpa [coeff_C_mul_X, coeff_C] using this
    rw [← hx, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx0
    rw [← hy, ZMod.intCast_zmod_eq_zero_iff_dvd] at hy0
    exact rem_not_both_zero ⟨a.val, ZMod.val_lt a⟩ ⟨b.val, ZMod.val_lt b⟩
      ⟨by simpa using hx0, by simpa using hy0⟩
  · have hdeg : (C x * X + C y : (ZMod 67)[X]).natDegree = 2 + (h - quot2 a b).natDegree := by
      rw [key, hg_monic.natDegree_mul' hs, hg_deg]
    have hle : (C x * X + C y : (ZMod 67)[X]).natDegree ≤ 1 := natDegree_linear_le
    omega

/-! ### Irreducibility -/

/-- A monic polynomial of degree 2 is `X² + c₁X + c₀`. -/
lemma monic_quadratic_eq {q : (ZMod 67)[X]} (hq : q.Monic) (hd : q.natDegree = 2) :
    q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
  have h2 : q.coeff 2 = 1 := by rw [← hd]; exact hq.coeff_natDegree
  conv_lhs => rw [as_sum_range' q 3 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ← C_mul_X_pow_eq_monomial, h2, map_one,
    one_mul, pow_zero, mul_one, pow_one]
  ring

/-- **`R` is irreducible modulo 67.** -/
theorem R67_irreducible : Irreducible R67 := by
  rw [R67_monic.irreducible_iff_lt_natDegree_lt R67_ne_one]
  intro q hq hdeg hdvd
  rw [R67_natDegree, Finset.mem_Ioc] at hdeg
  have h12 : q.natDegree = 1 ∨ q.natDegree = 2 := by
    have : (5 : ℕ) / 2 = 2 := by norm_num
    omega
  rcases h12 with h1 | h2
  · -- a monic linear factor `X + c` has the root `-c`
    have hq1 : q = X + C (q.coeff 0) := hq.eq_X_add_C h1
    have hroot : q.IsRoot (-(q.coeff 0)) := by
      rw [hq1]; simp [IsRoot]
    exact R67_no_root _ (hroot.dvd hdvd)
  · exact R67_no_quad (q.coeff 1) (q.coeff 0) (by rwa [← monic_quadratic_eq hq h2])

/-- **`R` is irreducible over `ℤ`.** -/
theorem Rint_irreducible : Irreducible Rint :=
  Rint_monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 67)) Rint
    (by rw [Rint_map_67]; exact R67_irreducible)

/-- **`R` is irreducible over `ℚ`** (Gauss's lemma). -/
theorem Rrat_irreducible : Irreducible Rrat := by
  rw [← Rint_map_rat]
  exact (Rint_monic.irreducible_iff_irreducible_map_fraction_map).mp Rint_irreducible

/-- **The minimal polynomial over `ℚ` of any root of `R` is `R`**, in every field `L` of characteristic 0. -/
theorem minpoly_eq_Rrat {L : Type*} [Field L] [CharZero L] (w : L) (hw : aeval w Rrat = 0) :
    minpoly ℚ w = Rrat :=
  (minpoly.eq_of_irreducible_of_monic Rrat_irreducible hw Rrat_monic).symm

/-- A rational polynomial vanishing at a root of `R` (in a field of characteristic 0) is divisible by `R`. -/
theorem Rrat_dvd_of_aeval_eq_zero {L : Type*} [Field L] [CharZero L] (w : L) (hw : aeval w Rrat = 0)
    (p : ℚ[X]) (hp : aeval w p = 0) : Rrat ∣ p := by
  rw [← minpoly_eq_Rrat w hw]
  exact minpoly.dvd ℚ w hp

end BranchC.GradeA
