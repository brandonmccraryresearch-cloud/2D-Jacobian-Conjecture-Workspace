import Jacobian.A816C.Data
import Jacobian.A816C.Subst
import Jacobian.A816C.Cancel
import Jacobian.A816C.Pivot.P01
import Jacobian.A816C.Pivot.P02
import Jacobian.A816C.Pivot.P03
import Jacobian.A816C.Pivot.P04
import Jacobian.A816C.Pivot.P05
import Jacobian.A816C.Pivot.P06
import Jacobian.A816C.Pivot.P07
import Jacobian.A816C.Pivot.P08
import Jacobian.A816C.Pivot.P09
import Jacobian.A816C.Pivot.P10
import Jacobian.A816C.Pivot.P11
import Jacobian.A816C.Pivot.P12
import Jacobian.A816C.Pivot.P13
import Jacobian.A816C.Pivot.P14
import Jacobian.A816C.Pivot.P15
import Jacobian.A816C.Pivot.P16
import Jacobian.A816C.Pivot.P17
import Jacobian.A816C.Pivot.P18
import Jacobian.A816C.Pivot.P19
import Jacobian.A816C.Pivot.P20
import Jacobian.A816C.Pivot.P21
import Jacobian.A816C.Pivot.P22
import Jacobian.A816C.Pivot.P23
import Jacobian.A816C.Pivot.P24

/-! Route C pivot 25: b_1_1 (layer 2).
Proves x = phi(x) from the layer equations and earlier pivots. (generated) -/

namespace A816C.Pivot.P25
open Lean.Grind.CommRing BranchAb.ChartProof A816C A816C.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

variable {L : Type*} [Field L] [CharZero L]

-- substitution: earlier pivots -> phi, else identity
noncomputable def sig : Nat → Expr := fun v =>
  if v = 2 then phi_01
  else if v = 4 then phi_02
  else if v = 6 then phi_03
  else if v = 8 then phi_04
  else if v = 10 then phi_05
  else if v = 12 then phi_06
  else if v = 14 then phi_07
  else if v = 16 then phi_08
  else if v = 21 then phi_09
  else if v = 24 then phi_10
  else if v = 27 then phi_11
  else if v = 30 then phi_12
  else if v = 33 then phi_13
  else if v = 36 then phi_14
  else if v = 39 then phi_15
  else if v = 42 then phi_16
  else if v = 45 then phi_17
  else .var v

theorem sig_agree (ctx : Context L)
  (hf_01 : (Expr.var 2).denote ctx = phi_01.denote ctx)
  (hf_02 : (Expr.var 4).denote ctx = phi_02.denote ctx)
  (hf_03 : (Expr.var 6).denote ctx = phi_03.denote ctx)
  (hf_04 : (Expr.var 8).denote ctx = phi_04.denote ctx)
  (hf_05 : (Expr.var 10).denote ctx = phi_05.denote ctx)
  (hf_06 : (Expr.var 12).denote ctx = phi_06.denote ctx)
  (hf_07 : (Expr.var 14).denote ctx = phi_07.denote ctx)
  (hf_08 : (Expr.var 16).denote ctx = phi_08.denote ctx)
  (hf_09 : (Expr.var 21).denote ctx = phi_09.denote ctx)
  (hf_10 : (Expr.var 24).denote ctx = phi_10.denote ctx)
  (hf_11 : (Expr.var 27).denote ctx = phi_11.denote ctx)
  (hf_12 : (Expr.var 30).denote ctx = phi_12.denote ctx)
  (hf_13 : (Expr.var 33).denote ctx = phi_13.denote ctx)
  (hf_14 : (Expr.var 36).denote ctx = phi_14.denote ctx)
  (hf_15 : (Expr.var 39).denote ctx = phi_15.denote ctx)
  (hf_16 : (Expr.var 42).denote ctx = phi_16.denote ctx)
  (hf_17 : (Expr.var 45).denote ctx = phi_17.denote ctx)
  : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx := by
  intro v
  by_cases h1 : v = 2
  · subst h1
    simp only [sig]
    exact hf_01.symm
  ·
    by_cases h2 : v = 4
    · subst h2
      simp only [sig, h1]
      exact hf_02.symm
    ·
      by_cases h3 : v = 6
      · subst h3
        simp only [sig, h1, h2]
        exact hf_03.symm
      ·
        by_cases h4 : v = 8
        · subst h4
          simp only [sig, h1, h2, h3]
          exact hf_04.symm
        ·
          by_cases h5 : v = 10
          · subst h5
            simp only [sig, h1, h2, h3, h4]
            exact hf_05.symm
          ·
            by_cases h6 : v = 12
            · subst h6
              simp only [sig, h1, h2, h3, h4, h5]
              exact hf_06.symm
            ·
              by_cases h7 : v = 14
              · subst h7
                simp only [sig, h1, h2, h3, h4, h5, h6]
                exact hf_07.symm
              ·
                by_cases h8 : v = 16
                · subst h8
                  simp only [sig, h1, h2, h3, h4, h5, h6, h7]
                  exact hf_08.symm
                ·
                  by_cases h9 : v = 21
                  · subst h9
                    simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8]
                    exact hf_09.symm
                  ·
                    by_cases h10 : v = 24
                    · subst h10
                      simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9]
                      exact hf_10.symm
                    ·
                      by_cases h11 : v = 27
                      · subst h11
                        simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
                        exact hf_11.symm
                      ·
                        by_cases h12 : v = 30
                        · subst h12
                          simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
                          exact hf_12.symm
                        ·
                          by_cases h13 : v = 33
                          · subst h13
                            simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
                            exact hf_13.symm
                          ·
                            by_cases h14 : v = 36
                            · subst h14
                              simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
                              exact hf_14.symm
                            ·
                              by_cases h15 : v = 39
                              · subst h15
                                simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
                                exact hf_15.symm
                              ·
                                by_cases h16 : v = 42
                                · subst h16
                                  simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
                                  exact hf_16.symm
                                ·
                                  by_cases h17 : v = 45
                                  · subst h17
                                    simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
                                    exact hf_17.symm
                                  ·
                                    simp [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]

theorem expand_25_0 (ctx : Context L) :
    ff_25_0.denote ctx = (A816C.subst sig Ek_1_0).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_25_0 (A816C.subst sig Ek_1_0))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_25_0 (ctx : Context L) (hE : Ek_1_0.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_25_0.denote ctx = 0 := by
  rw [expand_25_0 ctx, A816C.denote_subst ctx sig Ek_1_0 hag, hE]

theorem tgt_25_zero (ctx : Context L) (hR : eR.denote ctx = 0)
  (hE_1_0 : Ek_1_0.denote ctx = 0)
  (hf_01 : (Expr.var 2).denote ctx = phi_01.denote ctx)
  (hf_02 : (Expr.var 4).denote ctx = phi_02.denote ctx)
  (hf_03 : (Expr.var 6).denote ctx = phi_03.denote ctx)
  (hf_04 : (Expr.var 8).denote ctx = phi_04.denote ctx)
  (hf_05 : (Expr.var 10).denote ctx = phi_05.denote ctx)
  (hf_06 : (Expr.var 12).denote ctx = phi_06.denote ctx)
  (hf_07 : (Expr.var 14).denote ctx = phi_07.denote ctx)
  (hf_08 : (Expr.var 16).denote ctx = phi_08.denote ctx)
  (hf_09 : (Expr.var 21).denote ctx = phi_09.denote ctx)
  (hf_10 : (Expr.var 24).denote ctx = phi_10.denote ctx)
  (hf_11 : (Expr.var 27).denote ctx = phi_11.denote ctx)
  (hf_12 : (Expr.var 30).denote ctx = phi_12.denote ctx)
  (hf_13 : (Expr.var 33).denote ctx = phi_13.denote ctx)
  (hf_14 : (Expr.var 36).denote ctx = phi_14.denote ctx)
  (hf_15 : (Expr.var 39).denote ctx = phi_15.denote ctx)
  (hf_16 : (Expr.var 42).denote ctx = phi_16.denote ctx)
  (hf_17 : (Expr.var 45).denote ctx = phi_17.denote ctx)
  : tgt_25.denote ctx = 0 := by
  have hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx :=
    sig_agree ctx hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  apply lc_zero ctx tgt_25 [(cc_25_0, ff_25_0), (gq_25, eR)]
  · decide +kernel
  · exact ⟨fz_25_0 ctx hE_1_0 hag, hR, trivial⟩

theorem fact_25 (ctx : Context L) (hR : eR.denote ctx = 0)
  (hE_1_0 : Ek_1_0.denote ctx = 0)
  (hf_01 : (Expr.var 2).denote ctx = phi_01.denote ctx)
  (hf_02 : (Expr.var 4).denote ctx = phi_02.denote ctx)
  (hf_03 : (Expr.var 6).denote ctx = phi_03.denote ctx)
  (hf_04 : (Expr.var 8).denote ctx = phi_04.denote ctx)
  (hf_05 : (Expr.var 10).denote ctx = phi_05.denote ctx)
  (hf_06 : (Expr.var 12).denote ctx = phi_06.denote ctx)
  (hf_07 : (Expr.var 14).denote ctx = phi_07.denote ctx)
  (hf_08 : (Expr.var 16).denote ctx = phi_08.denote ctx)
  (hf_09 : (Expr.var 21).denote ctx = phi_09.denote ctx)
  (hf_10 : (Expr.var 24).denote ctx = phi_10.denote ctx)
  (hf_11 : (Expr.var 27).denote ctx = phi_11.denote ctx)
  (hf_12 : (Expr.var 30).denote ctx = phi_12.denote ctx)
  (hf_13 : (Expr.var 33).denote ctx = phi_13.denote ctx)
  (hf_14 : (Expr.var 36).denote ctx = phi_14.denote ctx)
  (hf_15 : (Expr.var 39).denote ctx = phi_15.denote ctx)
  (hf_16 : (Expr.var 42).denote ctx = phi_16.denote ctx)
  (hf_17 : (Expr.var 45).denote ctx = phi_17.denote ctx)
  : (Expr.var 19).denote ctx = phi_25.denote ctx := by
  exact A816C.pivot_fact ctx (1) (by decide) (.var 19) phi_25
    (tgt_25_zero ctx hR hE_1_0 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17)

end A816C.Pivot.P25
