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
import Jacobian.A816C.Pivot.P37
import Jacobian.A816C.Pivot.P38
import Jacobian.A816C.Pivot.P39
import Jacobian.A816C.Pivot.P40
import Jacobian.A816C.Pivot.P41
import Jacobian.A816C.Pivot.P42
import Jacobian.A816C.Pivot.P43
import Jacobian.A816C.Pivot.P44
import Jacobian.A816C.Pivot.P45
import Jacobian.A816C.Pivot.P46
import Jacobian.A816C.Pivot.P47

/-! Route C final assembly (generated).
From the final identity and all 47 pivot facts, concludes a_8,16 = 0. -/

namespace A816C.Final
open Lean.Grind.CommRing BranchAb.ChartProof A816C A816C.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

variable {L : Type*} [Field L] [CharZero L]

noncomputable def sigF : Nat → Expr := fun v =>
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
  else if v = 20 then phi_36
  else if v = 23 then phi_37
  else if v = 26 then phi_38
  else if v = 29 then phi_39
  else if v = 32 then phi_40
  else if v = 35 then phi_41
  else if v = 38 then phi_42
  else if v = 41 then phi_43
  else if v = 44 then phi_44
  else if v = 47 then phi_45
  else if v = 50 then phi_46
  else if v = 53 then phi_47
  else .var v

theorem sigF_agree (ctx : Context L)
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
  (hf_36 : (Expr.var 20).denote ctx = phi_36.denote ctx)
  (hf_37 : (Expr.var 23).denote ctx = phi_37.denote ctx)
  (hf_38 : (Expr.var 26).denote ctx = phi_38.denote ctx)
  (hf_39 : (Expr.var 29).denote ctx = phi_39.denote ctx)
  (hf_40 : (Expr.var 32).denote ctx = phi_40.denote ctx)
  (hf_41 : (Expr.var 35).denote ctx = phi_41.denote ctx)
  (hf_42 : (Expr.var 38).denote ctx = phi_42.denote ctx)
  (hf_43 : (Expr.var 41).denote ctx = phi_43.denote ctx)
  (hf_44 : (Expr.var 44).denote ctx = phi_44.denote ctx)
  (hf_45 : (Expr.var 47).denote ctx = phi_45.denote ctx)
  (hf_46 : (Expr.var 50).denote ctx = phi_46.denote ctx)
  (hf_47 : (Expr.var 53).denote ctx = phi_47.denote ctx)
  : ∀ v, (sigF v).denote ctx = (Expr.var v).denote ctx := by
  intro v
  by_cases h1 : v = 2
  · subst h1
    simp only [sigF]
    exact hf_01.symm
  ·
    by_cases h2 : v = 4
    · subst h2
      simp only [sigF, h1]
      exact hf_02.symm
    ·
      by_cases h3 : v = 6
      · subst h3
        simp only [sigF, h1, h2]
        exact hf_03.symm
      ·
        by_cases h4 : v = 8
        · subst h4
          simp only [sigF, h1, h2, h3]
          exact hf_04.symm
        ·
          by_cases h5 : v = 10
          · subst h5
            simp only [sigF, h1, h2, h3, h4]
            exact hf_05.symm
          ·
            by_cases h6 : v = 12
            · subst h6
              simp only [sigF, h1, h2, h3, h4, h5]
              exact hf_06.symm
            ·
              by_cases h7 : v = 14
              · subst h7
                simp only [sigF, h1, h2, h3, h4, h5, h6]
                exact hf_07.symm
              ·
                by_cases h8 : v = 16
                · subst h8
                  simp only [sigF, h1, h2, h3, h4, h5, h6, h7]
                  exact hf_08.symm
                ·
                  by_cases h9 : v = 21
                  · subst h9
                    simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8]
                    exact hf_09.symm
                  ·
                    by_cases h10 : v = 24
                    · subst h10
                      simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9]
                      exact hf_10.symm
                    ·
                      by_cases h11 : v = 27
                      · subst h11
                        simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
                        exact hf_11.symm
                      ·
                        by_cases h12 : v = 30
                        · subst h12
                          simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
                          exact hf_12.symm
                        ·
                          by_cases h13 : v = 33
                          · subst h13
                            simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
                            exact hf_13.symm
                          ·
                            by_cases h14 : v = 36
                            · subst h14
                              simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
                              exact hf_14.symm
                            ·
                              by_cases h15 : v = 39
                              · subst h15
                                simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
                                exact hf_15.symm
                              ·
                                by_cases h16 : v = 42
                                · subst h16
                                  simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
                                  exact hf_16.symm
                                ·
                                  by_cases h17 : v = 45
                                  · subst h17
                                    simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
                                    exact hf_17.symm
                                  ·
                                    by_cases h18 : v = 3
                                    · subst h18
                                      simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
                                      exact hf_18.symm
                                    ·
                                      by_cases h19 : v = 5
                                      · subst h19
                                        simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
                                        exact hf_19.symm
                                      ·
                                        by_cases h20 : v = 7
                                        · subst h20
                                          simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
                                          exact hf_20.symm
                                        ·
                                          by_cases h21 : v = 9
                                          · subst h21
                                            simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
                                            exact hf_21.symm
                                          ·
                                            by_cases h22 : v = 11
                                            · subst h22
                                              simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
                                              exact hf_22.symm
                                            ·
                                              by_cases h23 : v = 13
                                              · subst h23
                                                simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
                                                exact hf_23.symm
                                              ·
                                                by_cases h24 : v = 15
                                                · subst h24
                                                  simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
                                                  exact hf_24.symm
                                                ·
                                                  by_cases h25 : v = 19
                                                  · subst h25
                                                    simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
                                                    exact hf_25.symm
                                                  ·
                                                    by_cases h26 : v = 22
                                                    · subst h26
                                                      simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
                                                      exact hf_26.symm
                                                    ·
                                                      by_cases h27 : v = 25
                                                      · subst h27
                                                        simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
                                                        exact hf_27.symm
                                                      ·
                                                        by_cases h28 : v = 28
                                                        · subst h28
                                                          simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
                                                          exact hf_28.symm
                                                        ·
                                                          by_cases h29 : v = 31
                                                          · subst h29
                                                            simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
                                                            exact hf_29.symm
                                                          ·
                                                            by_cases h30 : v = 34
                                                            · subst h30
                                                              simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
                                                              exact hf_30.symm
                                                            ·
                                                              by_cases h31 : v = 37
                                                              · subst h31
                                                                simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
                                                                exact hf_31.symm
                                                              ·
                                                                by_cases h32 : v = 40
                                                                · subst h32
                                                                  simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
                                                                  exact hf_32.symm
                                                                ·
                                                                  by_cases h33 : v = 43
                                                                  · subst h33
                                                                    simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
                                                                    exact hf_33.symm
                                                                  ·
                                                                    by_cases h34 : v = 46
                                                                    · subst h34
                                                                      simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
                                                                      exact hf_34.symm
                                                                    ·
                                                                      by_cases h35 : v = 52
                                                                      · subst h35
                                                                        simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
                                                                        exact hf_35.symm
                                                                      ·
                                                                        by_cases h36 : v = 20
                                                                        · subst h36
                                                                          simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
                                                                          exact hf_36.symm
                                                                        ·
                                                                          by_cases h37 : v = 23
                                                                          · subst h37
                                                                            simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
                                                                            exact hf_37.symm
                                                                          ·
                                                                            by_cases h38 : v = 26
                                                                            · subst h38
                                                                              simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37]
                                                                              exact hf_38.symm
                                                                            ·
                                                                              by_cases h39 : v = 29
                                                                              · subst h39
                                                                                simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38]
                                                                                exact hf_39.symm
                                                                              ·
                                                                                by_cases h40 : v = 32
                                                                                · subst h40
                                                                                  simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39]
                                                                                  exact hf_40.symm
                                                                                ·
                                                                                  by_cases h41 : v = 35
                                                                                  · subst h41
                                                                                    simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40]
                                                                                    exact hf_41.symm
                                                                                  ·
                                                                                    by_cases h42 : v = 38
                                                                                    · subst h42
                                                                                      simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41]
                                                                                      exact hf_42.symm
                                                                                    ·
                                                                                      by_cases h43 : v = 41
                                                                                      · subst h43
                                                                                        simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42]
                                                                                        exact hf_43.symm
                                                                                      ·
                                                                                        by_cases h44 : v = 44
                                                                                        · subst h44
                                                                                          simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43]
                                                                                          exact hf_44.symm
                                                                                        ·
                                                                                          by_cases h45 : v = 47
                                                                                          · subst h45
                                                                                            simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44]
                                                                                            exact hf_45.symm
                                                                                          ·
                                                                                            by_cases h46 : v = 50
                                                                                            · subst h46
                                                                                              simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45]
                                                                                              exact hf_46.symm
                                                                                            ·
                                                                                              by_cases h47 : v = 53
                                                                                              · subst h47
                                                                                                simp only [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46]
                                                                                                exact hf_47.symm
                                                                                              ·
                                                                                                simp [sigF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47]

theorem expandF_0 (ctx : Context L) :
    ffF_0.denote ctx = (A816C.subst sigF Ek_13_25).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ffF_0 (A816C.subst sigF Ek_13_25))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fzF_0 (ctx : Context L) (hE : Ek_13_25.denote ctx = 0)
    (hag : ∀ v, (sigF v).denote ctx = (Expr.var v).denote ctx) :
    ffF_0.denote ctx = 0 := by
  rw [expandF_0 ctx, A816C.denote_subst ctx sigF Ek_13_25 hag, hE]

theorem expandF_1 (ctx : Context L) :
    ffF_1.denote ctx = (A816C.subst sigF Ek_14_27).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ffF_1 (A816C.subst sigF Ek_14_27))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fzF_1 (ctx : Context L) (hE : Ek_14_27.denote ctx = 0)
    (hag : ∀ v, (sigF v).denote ctx = (Expr.var v).denote ctx) :
    ffF_1.denote ctx = 0 := by
  rw [expandF_1 ctx, A816C.denote_subst ctx sigF Ek_14_27 hag, hE]

theorem expandF_2 (ctx : Context L) :
    ffF_2.denote ctx = (A816C.subst sigF Ek_15_29).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ffF_2 (A816C.subst sigF Ek_15_29))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fzF_2 (ctx : Context L) (hE : Ek_15_29.denote ctx = 0)
    (hag : ∀ v, (sigF v).denote ctx = (Expr.var v).denote ctx) :
    ffF_2.denote ctx = 0 := by
  rw [expandF_2 ctx, A816C.denote_subst ctx sigF Ek_15_29 hag, hE]

theorem expandF_3 (ctx : Context L) :
    ffF_3.denote ctx = (A816C.subst sigF Ek_16_31).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ffF_3 (A816C.subst sigF Ek_16_31))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fzF_3 (ctx : Context L) (hE : Ek_16_31.denote ctx = 0)
    (hag : ∀ v, (sigF v).denote ctx = (Expr.var v).denote ctx) :
    ffF_3.denote ctx = 0 := by
  rw [expandF_3 ctx, A816C.denote_subst ctx sigF Ek_16_31 hag, hE]

theorem expandF_4 (ctx : Context L) :
    ffF_4.denote ctx = (A816C.subst sigF Ek_17_33).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ffF_4 (A816C.subst sigF Ek_17_33))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fzF_4 (ctx : Context L) (hE : Ek_17_33.denote ctx = 0)
    (hag : ∀ v, (sigF v).denote ctx = (Expr.var v).denote ctx) :
    ffF_4.denote ctx = 0 := by
  rw [expandF_4 ctx, A816C.denote_subst ctx sigF Ek_17_33 hag, hE]

theorem expandF_5 (ctx : Context L) :
    ffF_5.denote ctx = (A816C.subst sigF Ek_18_35).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ffF_5 (A816C.subst sigF Ek_18_35))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fzF_5 (ctx : Context L) (hE : Ek_18_35.denote ctx = 0)
    (hag : ∀ v, (sigF v).denote ctx = (Expr.var v).denote ctx) :
    ffF_5.denote ctx = 0 := by
  rw [expandF_5 ctx, A816C.denote_subst ctx sigF Ek_18_35 hag, hE]

theorem expandF_6 (ctx : Context L) :
    ffF_6.denote ctx = (A816C.subst sigF Ek_2_4).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ffF_6 (A816C.subst sigF Ek_2_4))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fzF_6 (ctx : Context L) (hE : Ek_2_4.denote ctx = 0)
    (hag : ∀ v, (sigF v).denote ctx = (Expr.var v).denote ctx) :
    ffF_6.denote ctx = 0 := by
  rw [expandF_6 ctx, A816C.denote_subst ctx sigF Ek_2_4 hag, hE]

theorem expandF_7 (ctx : Context L) :
    ffF_7.denote ctx = (A816C.subst sigF Ek_3_6).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ffF_7 (A816C.subst sigF Ek_3_6))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fzF_7 (ctx : Context L) (hE : Ek_3_6.denote ctx = 0)
    (hag : ∀ v, (sigF v).denote ctx = (Expr.var v).denote ctx) :
    ffF_7.denote ctx = 0 := by
  rw [expandF_7 ctx, A816C.denote_subst ctx sigF Ek_3_6 hag, hE]

theorem expandF_8 (ctx : Context L) :
    ffF_8.denote ctx = (A816C.subst sigF Ek_4_8).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ffF_8 (A816C.subst sigF Ek_4_8))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fzF_8 (ctx : Context L) (hE : Ek_4_8.denote ctx = 0)
    (hag : ∀ v, (sigF v).denote ctx = (Expr.var v).denote ctx) :
    ffF_8.denote ctx = 0 := by
  rw [expandF_8 ctx, A816C.denote_subst ctx sigF Ek_4_8 hag, hE]

theorem tgtF_zero (ctx : Context L) (hR : eR.denote ctx = 0)
  (hE_13_25 : Ek_13_25.denote ctx = 0)
  (hE_14_27 : Ek_14_27.denote ctx = 0)
  (hE_15_29 : Ek_15_29.denote ctx = 0)
  (hE_16_31 : Ek_16_31.denote ctx = 0)
  (hE_17_33 : Ek_17_33.denote ctx = 0)
  (hE_18_35 : Ek_18_35.denote ctx = 0)
  (hE_2_4 : Ek_2_4.denote ctx = 0)
  (hE_3_6 : Ek_3_6.denote ctx = 0)
  (hE_4_8 : Ek_4_8.denote ctx = 0)
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
  (hf_36 : (Expr.var 20).denote ctx = phi_36.denote ctx)
  (hf_37 : (Expr.var 23).denote ctx = phi_37.denote ctx)
  (hf_38 : (Expr.var 26).denote ctx = phi_38.denote ctx)
  (hf_39 : (Expr.var 29).denote ctx = phi_39.denote ctx)
  (hf_40 : (Expr.var 32).denote ctx = phi_40.denote ctx)
  (hf_41 : (Expr.var 35).denote ctx = phi_41.denote ctx)
  (hf_42 : (Expr.var 38).denote ctx = phi_42.denote ctx)
  (hf_43 : (Expr.var 41).denote ctx = phi_43.denote ctx)
  (hf_44 : (Expr.var 44).denote ctx = phi_44.denote ctx)
  (hf_45 : (Expr.var 47).denote ctx = phi_45.denote ctx)
  (hf_46 : (Expr.var 50).denote ctx = phi_46.denote ctx)
  (hf_47 : (Expr.var 53).denote ctx = phi_47.denote ctx)
  : tgtF.denote ctx = 0 := by
  have hag : ∀ v, (sigF v).denote ctx = (Expr.var v).denote ctx :=
    sigF_agree ctx hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31 hf_32 hf_33 hf_34 hf_35 hf_36 hf_37 hf_38 hf_39 hf_40 hf_41 hf_42 hf_43 hf_44 hf_45 hf_46 hf_47
  apply lc_zero ctx tgtF [(hhF_0, ffF_0), (hhF_1, ffF_1), (hhF_2, ffF_2), (hhF_3, ffF_3), (hhF_4, ffF_4), (hhF_5, ffF_5), (hhF_6, ffF_6), (hhF_7, ffF_7), (hhF_8, ffF_8), (gqF, eR)]
  · decide +kernel
  · exact ⟨fzF_0 ctx hE_13_25 hag, fzF_1 ctx hE_14_27 hag, fzF_2 ctx hE_15_29 hag, fzF_3 ctx hE_16_31 hag, fzF_4 ctx hE_17_33 hag, fzF_5 ctx hE_18_35 hag, fzF_6 ctx hE_2_4 hag, fzF_7 ctx hE_3_6 hag, fzF_8 ctx hE_4_8 hag, hR, trivial⟩

-- tgtF = 183677021503809136615621596412610404650462974988093609547183594954618005827417676421828186931842958399644319605581094609894601795344362055971000135843462860583539040403879361628635446367393735009003754791217632581828325446150135411915314793464140223761858193244398795414604737079394212684917220330749938958462171943186740466123989837286713499543218713188534714912218956291519520268807771232437716835156389674078309908504276337697616668426187468335533260800000 * a_8_16^2; cancel to get a_8_16 = 0
theorem a816_zero (ctx : Context L) (hR : eR.denote ctx = 0)
  (hE_13_25 : Ek_13_25.denote ctx = 0)
  (hE_14_27 : Ek_14_27.denote ctx = 0)
  (hE_15_29 : Ek_15_29.denote ctx = 0)
  (hE_16_31 : Ek_16_31.denote ctx = 0)
  (hE_17_33 : Ek_17_33.denote ctx = 0)
  (hE_18_35 : Ek_18_35.denote ctx = 0)
  (hE_2_4 : Ek_2_4.denote ctx = 0)
  (hE_3_6 : Ek_3_6.denote ctx = 0)
  (hE_4_8 : Ek_4_8.denote ctx = 0)
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
  (hf_36 : (Expr.var 20).denote ctx = phi_36.denote ctx)
  (hf_37 : (Expr.var 23).denote ctx = phi_37.denote ctx)
  (hf_38 : (Expr.var 26).denote ctx = phi_38.denote ctx)
  (hf_39 : (Expr.var 29).denote ctx = phi_39.denote ctx)
  (hf_40 : (Expr.var 32).denote ctx = phi_40.denote ctx)
  (hf_41 : (Expr.var 35).denote ctx = phi_41.denote ctx)
  (hf_42 : (Expr.var 38).denote ctx = phi_42.denote ctx)
  (hf_43 : (Expr.var 41).denote ctx = phi_43.denote ctx)
  (hf_44 : (Expr.var 44).denote ctx = phi_44.denote ctx)
  (hf_45 : (Expr.var 47).denote ctx = phi_45.denote ctx)
  (hf_46 : (Expr.var 50).denote ctx = phi_46.denote ctx)
  (hf_47 : (Expr.var 53).denote ctx = phi_47.denote ctx)
  : (Expr.var 17).denote ctx = 0 := by
  have hz := tgtF_zero ctx hR hE_13_25 hE_14_27 hE_15_29 hE_16_31 hE_17_33 hE_18_35 hE_2_4 hE_3_6 hE_4_8 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31 hf_32 hf_33 hf_34 hf_35 hf_36 hf_37 hf_38 hf_39 hf_40 hf_41 hf_42 hf_43 hf_44 hf_45 hf_46 hf_47
  have h1 : ((Expr.pow (.var 17) 2 : Expr)).denote ctx = 0 :=
    A816C.cancel_int ctx _ (183677021503809136615621596412610404650462974988093609547183594954618005827417676421828186931842958399644319605581094609894601795344362055971000135843462860583539040403879361628635446367393735009003754791217632581828325446150135411915314793464140223761858193244398795414604737079394212684917220330749938958462171943186740466123989837286713499543218713188534714912218956291519520268807771232437716835156389674078309908504276337697616668426187468335533260800000) (by decide) hz
  have h2 : ((Expr.var 17).denote ctx) ^ 2 = 0 := h1
  exact (pow_eq_zero_iff (show (2:ℕ) ≠ 0 by decide)).mp h2

end A816C.Final
