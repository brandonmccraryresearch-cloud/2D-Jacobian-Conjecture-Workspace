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
import Jacobian.A816C.Pivot.P25
import Jacobian.A816C.Pivot.P26
import Jacobian.A816C.Pivot.P27
import Jacobian.A816C.Pivot.P28
import Jacobian.A816C.Pivot.P29
import Jacobian.A816C.Pivot.P30
import Jacobian.A816C.Pivot.P31
import Jacobian.A816C.Pivot.P32
import Jacobian.A816C.Pivot.P33
import Jacobian.A816C.Pivot.P34
import Jacobian.A816C.Pivot.P35
import Jacobian.A816C.Pivot.P36

/-! Route C pivot 37: b_2_4 (layer 1).
Proves x = phi(x) from the layer equations and earlier pivots. (generated) -/

namespace A816C.Pivot.P37
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
  else if v = 3 then phi_18
  else if v = 5 then phi_19
  else if v = 7 then phi_20
  else if v = 9 then phi_21
  else if v = 11 then phi_22
  else if v = 13 then phi_23
  else if v = 15 then phi_24
  else if v = 19 then phi_25
  else if v = 22 then phi_26
  else if v = 25 then phi_27
  else if v = 28 then phi_28
  else if v = 31 then phi_29
  else if v = 34 then phi_30
  else if v = 37 then phi_31
  else if v = 40 then phi_32
  else if v = 43 then phi_33
  else if v = 46 then phi_34
  else if v = 52 then phi_35
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
  (hf_18 : (Expr.var 3).denote ctx = phi_18.denote ctx)
  (hf_19 : (Expr.var 5).denote ctx = phi_19.denote ctx)
  (hf_20 : (Expr.var 7).denote ctx = phi_20.denote ctx)
  (hf_21 : (Expr.var 9).denote ctx = phi_21.denote ctx)
  (hf_22 : (Expr.var 11).denote ctx = phi_22.denote ctx)
  (hf_23 : (Expr.var 13).denote ctx = phi_23.denote ctx)
  (hf_24 : (Expr.var 15).denote ctx = phi_24.denote ctx)
  (hf_25 : (Expr.var 19).denote ctx = phi_25.denote ctx)
  (hf_26 : (Expr.var 22).denote ctx = phi_26.denote ctx)
  (hf_27 : (Expr.var 25).denote ctx = phi_27.denote ctx)
  (hf_28 : (Expr.var 28).denote ctx = phi_28.denote ctx)
  (hf_29 : (Expr.var 31).denote ctx = phi_29.denote ctx)
  (hf_30 : (Expr.var 34).denote ctx = phi_30.denote ctx)
  (hf_31 : (Expr.var 37).denote ctx = phi_31.denote ctx)
  (hf_32 : (Expr.var 40).denote ctx = phi_32.denote ctx)
  (hf_33 : (Expr.var 43).denote ctx = phi_33.denote ctx)
  (hf_34 : (Expr.var 46).denote ctx = phi_34.denote ctx)
  (hf_35 : (Expr.var 52).denote ctx = phi_35.denote ctx)
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
                                    by_cases h18 : v = 3
                                    · subst h18
                                      simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
                                      exact hf_18.symm
                                    ·
                                      by_cases h19 : v = 5
                                      · subst h19
                                        simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
                                        exact hf_19.symm
                                      ·
                                        by_cases h20 : v = 7
                                        · subst h20
                                          simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
                                          exact hf_20.symm
                                        ·
                                          by_cases h21 : v = 9
                                          · subst h21
                                            simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
                                            exact hf_21.symm
                                          ·
                                            by_cases h22 : v = 11
                                            · subst h22
                                              simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
                                              exact hf_22.symm
                                            ·
                                              by_cases h23 : v = 13
                                              · subst h23
                                                simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
                                                exact hf_23.symm
                                              ·
                                                by_cases h24 : v = 15
                                                · subst h24
                                                  simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
                                                  exact hf_24.symm
                                                ·
                                                  by_cases h25 : v = 19
                                                  · subst h25
                                                    simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
                                                    exact hf_25.symm
                                                  ·
                                                    by_cases h26 : v = 22
                                                    · subst h26
                                                      simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
                                                      exact hf_26.symm
                                                    ·
                                                      by_cases h27 : v = 25
                                                      · subst h27
                                                        simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
                                                        exact hf_27.symm
                                                      ·
                                                        by_cases h28 : v = 28
                                                        · subst h28
                                                          simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
                                                          exact hf_28.symm
                                                        ·
                                                          by_cases h29 : v = 31
                                                          · subst h29
                                                            simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
                                                            exact hf_29.symm
                                                          ·
                                                            by_cases h30 : v = 34
                                                            · subst h30
                                                              simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
                                                              exact hf_30.symm
                                                            ·
                                                              by_cases h31 : v = 37
                                                              · subst h31
                                                                simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
                                                                exact hf_31.symm
                                                              ·
                                                                by_cases h32 : v = 40
                                                                · subst h32
                                                                  simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
                                                                  exact hf_32.symm
                                                                ·
                                                                  by_cases h33 : v = 43
                                                                  · subst h33
                                                                    simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
                                                                    exact hf_33.symm
                                                                  ·
                                                                    by_cases h34 : v = 46
                                                                    · subst h34
                                                                      simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
                                                                      exact hf_34.symm
                                                                    ·
                                                                      by_cases h35 : v = 52
                                                                      · subst h35
                                                                        simp only [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
                                                                        exact hf_35.symm
                                                                      ·
                                                                        simp [sig, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]

theorem expand_37_0 (ctx : Context L) :
    ff_37_0.denote ctx = (A816C.subst sig Ek_1_1).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_37_0 (A816C.subst sig Ek_1_1))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_37_0 (ctx : Context L) (hE : Ek_1_1.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_37_0.denote ctx = 0 := by
  rw [expand_37_0 ctx, A816C.denote_subst ctx sig Ek_1_1 hag, hE]

theorem expand_37_1 (ctx : Context L) :
    ff_37_1.denote ctx = (A816C.subst sig Ek_2_3).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_37_1 (A816C.subst sig Ek_2_3))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_37_1 (ctx : Context L) (hE : Ek_2_3.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_37_1.denote ctx = 0 := by
  rw [expand_37_1 ctx, A816C.denote_subst ctx sig Ek_2_3 hag, hE]

theorem tgt_37_zero (ctx : Context L) (hR : eR.denote ctx = 0)
  (hE_1_1 : Ek_1_1.denote ctx = 0)
  (hE_2_3 : Ek_2_3.denote ctx = 0)
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
  (hf_18 : (Expr.var 3).denote ctx = phi_18.denote ctx)
  (hf_19 : (Expr.var 5).denote ctx = phi_19.denote ctx)
  (hf_20 : (Expr.var 7).denote ctx = phi_20.denote ctx)
  (hf_21 : (Expr.var 9).denote ctx = phi_21.denote ctx)
  (hf_22 : (Expr.var 11).denote ctx = phi_22.denote ctx)
  (hf_23 : (Expr.var 13).denote ctx = phi_23.denote ctx)
  (hf_24 : (Expr.var 15).denote ctx = phi_24.denote ctx)
  (hf_25 : (Expr.var 19).denote ctx = phi_25.denote ctx)
  (hf_26 : (Expr.var 22).denote ctx = phi_26.denote ctx)
  (hf_27 : (Expr.var 25).denote ctx = phi_27.denote ctx)
  (hf_28 : (Expr.var 28).denote ctx = phi_28.denote ctx)
  (hf_29 : (Expr.var 31).denote ctx = phi_29.denote ctx)
  (hf_30 : (Expr.var 34).denote ctx = phi_30.denote ctx)
  (hf_31 : (Expr.var 37).denote ctx = phi_31.denote ctx)
  (hf_32 : (Expr.var 40).denote ctx = phi_32.denote ctx)
  (hf_33 : (Expr.var 43).denote ctx = phi_33.denote ctx)
  (hf_34 : (Expr.var 46).denote ctx = phi_34.denote ctx)
  (hf_35 : (Expr.var 52).denote ctx = phi_35.denote ctx)
  : tgt_37.denote ctx = 0 := by
  have hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx :=
    sig_agree ctx hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31 hf_32 hf_33 hf_34 hf_35
  apply lc_zero ctx tgt_37 [(cc_37_0, ff_37_0), (cc_37_1, ff_37_1), (gq_37, eR)]
  · decide +kernel
  · exact ⟨fz_37_0 ctx hE_1_1 hag, fz_37_1 ctx hE_2_3 hag, hR, trivial⟩

theorem fact_37 (ctx : Context L) (hR : eR.denote ctx = 0)
  (hE_1_1 : Ek_1_1.denote ctx = 0)
  (hE_2_3 : Ek_2_3.denote ctx = 0)
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
  (hf_18 : (Expr.var 3).denote ctx = phi_18.denote ctx)
  (hf_19 : (Expr.var 5).denote ctx = phi_19.denote ctx)
  (hf_20 : (Expr.var 7).denote ctx = phi_20.denote ctx)
  (hf_21 : (Expr.var 9).denote ctx = phi_21.denote ctx)
  (hf_22 : (Expr.var 11).denote ctx = phi_22.denote ctx)
  (hf_23 : (Expr.var 13).denote ctx = phi_23.denote ctx)
  (hf_24 : (Expr.var 15).denote ctx = phi_24.denote ctx)
  (hf_25 : (Expr.var 19).denote ctx = phi_25.denote ctx)
  (hf_26 : (Expr.var 22).denote ctx = phi_26.denote ctx)
  (hf_27 : (Expr.var 25).denote ctx = phi_27.denote ctx)
  (hf_28 : (Expr.var 28).denote ctx = phi_28.denote ctx)
  (hf_29 : (Expr.var 31).denote ctx = phi_29.denote ctx)
  (hf_30 : (Expr.var 34).denote ctx = phi_30.denote ctx)
  (hf_31 : (Expr.var 37).denote ctx = phi_31.denote ctx)
  (hf_32 : (Expr.var 40).denote ctx = phi_32.denote ctx)
  (hf_33 : (Expr.var 43).denote ctx = phi_33.denote ctx)
  (hf_34 : (Expr.var 46).denote ctx = phi_34.denote ctx)
  (hf_35 : (Expr.var 52).denote ctx = phi_35.denote ctx)
  : (Expr.var 23).denote ctx = phi_37.denote ctx := by
  exact A816C.pivot_fact ctx (512) (by decide) (.var 23) phi_37
    (tgt_37_zero ctx hR hE_1_1 hE_2_3 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31 hf_32 hf_33 hf_34 hf_35)

end A816C.Pivot.P37
