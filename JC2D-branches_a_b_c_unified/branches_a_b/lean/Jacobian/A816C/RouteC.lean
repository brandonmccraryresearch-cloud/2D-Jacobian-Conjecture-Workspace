import Jacobian.A816C.Final

/-! Route C top-level theorem (generated).
Independent kernel-checked proof that a_8,16 = 0 from the 75 layer equations,
not using the descent. -/

namespace A816C
open Lean.Grind.CommRing BranchAb.ChartProof A816C.Data

variable {L : Type*} [Field L] [CharZero L]

theorem routeC_a816 (ctx : Context L) (hR : A816C.Data.eR.denote ctx = 0)
  (hE_1_0 : A816C.Data.Ek_1_0.denote ctx = 0)
  (hE_1_1 : A816C.Data.Ek_1_1.denote ctx = 0)
  (hE_1_2 : A816C.Data.Ek_1_2.denote ctx = 0)
  (hE_2_1 : A816C.Data.Ek_2_1.denote ctx = 0)
  (hE_2_2 : A816C.Data.Ek_2_2.denote ctx = 0)
  (hE_2_3 : A816C.Data.Ek_2_3.denote ctx = 0)
  (hE_2_4 : A816C.Data.Ek_2_4.denote ctx = 0)
  (hE_3_3 : A816C.Data.Ek_3_3.denote ctx = 0)
  (hE_3_4 : A816C.Data.Ek_3_4.denote ctx = 0)
  (hE_3_5 : A816C.Data.Ek_3_5.denote ctx = 0)
  (hE_3_6 : A816C.Data.Ek_3_6.denote ctx = 0)
  (hE_4_5 : A816C.Data.Ek_4_5.denote ctx = 0)
  (hE_4_6 : A816C.Data.Ek_4_6.denote ctx = 0)
  (hE_4_7 : A816C.Data.Ek_4_7.denote ctx = 0)
  (hE_4_8 : A816C.Data.Ek_4_8.denote ctx = 0)
  (hE_5_7 : A816C.Data.Ek_5_7.denote ctx = 0)
  (hE_5_8 : A816C.Data.Ek_5_8.denote ctx = 0)
  (hE_5_9 : A816C.Data.Ek_5_9.denote ctx = 0)
  (hE_5_10 : A816C.Data.Ek_5_10.denote ctx = 0)
  (hE_6_9 : A816C.Data.Ek_6_9.denote ctx = 0)
  (hE_6_10 : A816C.Data.Ek_6_10.denote ctx = 0)
  (hE_6_11 : A816C.Data.Ek_6_11.denote ctx = 0)
  (hE_6_12 : A816C.Data.Ek_6_12.denote ctx = 0)
  (hE_7_11 : A816C.Data.Ek_7_11.denote ctx = 0)
  (hE_7_12 : A816C.Data.Ek_7_12.denote ctx = 0)
  (hE_7_13 : A816C.Data.Ek_7_13.denote ctx = 0)
  (hE_7_14 : A816C.Data.Ek_7_14.denote ctx = 0)
  (hE_8_13 : A816C.Data.Ek_8_13.denote ctx = 0)
  (hE_8_14 : A816C.Data.Ek_8_14.denote ctx = 0)
  (hE_8_15 : A816C.Data.Ek_8_15.denote ctx = 0)
  (hE_8_16 : A816C.Data.Ek_8_16.denote ctx = 0)
  (hE_9_15 : A816C.Data.Ek_9_15.denote ctx = 0)
  (hE_9_16 : A816C.Data.Ek_9_16.denote ctx = 0)
  (hE_9_17 : A816C.Data.Ek_9_17.denote ctx = 0)
  (hE_9_18 : A816C.Data.Ek_9_18.denote ctx = 0)
  (hE_10_17 : A816C.Data.Ek_10_17.denote ctx = 0)
  (hE_10_18 : A816C.Data.Ek_10_18.denote ctx = 0)
  (hE_10_19 : A816C.Data.Ek_10_19.denote ctx = 0)
  (hE_10_20 : A816C.Data.Ek_10_20.denote ctx = 0)
  (hE_11_19 : A816C.Data.Ek_11_19.denote ctx = 0)
  (hE_11_20 : A816C.Data.Ek_11_20.denote ctx = 0)
  (hE_11_21 : A816C.Data.Ek_11_21.denote ctx = 0)
  (hE_11_22 : A816C.Data.Ek_11_22.denote ctx = 0)
  (hE_12_21 : A816C.Data.Ek_12_21.denote ctx = 0)
  (hE_12_22 : A816C.Data.Ek_12_22.denote ctx = 0)
  (hE_12_23 : A816C.Data.Ek_12_23.denote ctx = 0)
  (hE_12_24 : A816C.Data.Ek_12_24.denote ctx = 0)
  (hE_13_23 : A816C.Data.Ek_13_23.denote ctx = 0)
  (hE_13_24 : A816C.Data.Ek_13_24.denote ctx = 0)
  (hE_13_25 : A816C.Data.Ek_13_25.denote ctx = 0)
  (hE_13_26 : A816C.Data.Ek_13_26.denote ctx = 0)
  (hE_14_25 : A816C.Data.Ek_14_25.denote ctx = 0)
  (hE_14_26 : A816C.Data.Ek_14_26.denote ctx = 0)
  (hE_14_27 : A816C.Data.Ek_14_27.denote ctx = 0)
  (hE_14_28 : A816C.Data.Ek_14_28.denote ctx = 0)
  (hE_15_27 : A816C.Data.Ek_15_27.denote ctx = 0)
  (hE_15_28 : A816C.Data.Ek_15_28.denote ctx = 0)
  (hE_15_29 : A816C.Data.Ek_15_29.denote ctx = 0)
  (hE_15_30 : A816C.Data.Ek_15_30.denote ctx = 0)
  (hE_16_29 : A816C.Data.Ek_16_29.denote ctx = 0)
  (hE_16_30 : A816C.Data.Ek_16_30.denote ctx = 0)
  (hE_16_31 : A816C.Data.Ek_16_31.denote ctx = 0)
  (hE_16_32 : A816C.Data.Ek_16_32.denote ctx = 0)
  (hE_17_31 : A816C.Data.Ek_17_31.denote ctx = 0)
  (hE_17_32 : A816C.Data.Ek_17_32.denote ctx = 0)
  (hE_17_33 : A816C.Data.Ek_17_33.denote ctx = 0)
  (hE_17_34 : A816C.Data.Ek_17_34.denote ctx = 0)
  (hE_18_33 : A816C.Data.Ek_18_33.denote ctx = 0)
  (hE_18_34 : A816C.Data.Ek_18_34.denote ctx = 0)
  (hE_18_35 : A816C.Data.Ek_18_35.denote ctx = 0)
  (hE_18_36 : A816C.Data.Ek_18_36.denote ctx = 0)
  (hE_19_35 : A816C.Data.Ek_19_35.denote ctx = 0)
  (hE_19_36 : A816C.Data.Ek_19_36.denote ctx = 0)
  (hE_19_37 : A816C.Data.Ek_19_37.denote ctx = 0)
  (hE_19_38 : A816C.Data.Ek_19_38.denote ctx = 0)
  : (Expr.var 17).denote ctx = 0 := by
  have hf_01 : (Expr.var 2).denote ctx = A816C.Data.phi_01.denote ctx :=
    A816C.Pivot.P01.fact_01 ctx hR hE_2_1 hE_3_3 hE_4_5 hE_5_7 hE_6_9 hE_7_11 hE_8_13 hE_9_15 hE_10_17 hE_11_19 hE_12_21 hE_13_23 hE_14_25 hE_15_27 hE_16_29 hE_17_31 hE_18_33 
  have hf_02 : (Expr.var 4).denote ctx = A816C.Data.phi_02.denote ctx :=
    A816C.Pivot.P02.fact_02 ctx hR hE_2_1 hE_3_3 hE_4_5 hE_5_7 hE_6_9 hE_7_11 hE_8_13 hE_9_15 hE_10_17 hE_11_19 hE_12_21 hE_13_23 hE_14_25 hE_15_27 hE_16_29 hE_17_31 hE_18_33 
  have hf_03 : (Expr.var 6).denote ctx = A816C.Data.phi_03.denote ctx :=
    A816C.Pivot.P03.fact_03 ctx hR hE_2_1 hE_3_3 hE_4_5 hE_5_7 hE_6_9 hE_7_11 hE_8_13 hE_9_15 hE_10_17 hE_11_19 hE_12_21 hE_13_23 hE_14_25 hE_15_27 hE_16_29 hE_17_31 hE_18_33 
  have hf_04 : (Expr.var 8).denote ctx = A816C.Data.phi_04.denote ctx :=
    A816C.Pivot.P04.fact_04 ctx hR hE_2_1 hE_3_3 hE_4_5 hE_5_7 hE_6_9 hE_7_11 hE_8_13 hE_9_15 hE_10_17 hE_11_19 hE_12_21 hE_13_23 hE_14_25 hE_15_27 hE_16_29 hE_17_31 hE_18_33 
  have hf_05 : (Expr.var 10).denote ctx = A816C.Data.phi_05.denote ctx :=
    A816C.Pivot.P05.fact_05 ctx hR hE_2_1 hE_3_3 hE_4_5 hE_5_7 hE_6_9 hE_7_11 hE_8_13 hE_9_15 hE_10_17 hE_11_19 hE_12_21 hE_13_23 hE_14_25 hE_15_27 hE_16_29 hE_17_31 hE_18_33 
  have hf_06 : (Expr.var 12).denote ctx = A816C.Data.phi_06.denote ctx :=
    A816C.Pivot.P06.fact_06 ctx hR hE_2_1 hE_3_3 hE_4_5 hE_5_7 hE_6_9 hE_7_11 hE_8_13 hE_9_15 hE_10_17 hE_11_19 hE_12_21 hE_13_23 hE_14_25 hE_15_27 hE_16_29 hE_17_31 hE_18_33 
  have hf_07 : (Expr.var 14).denote ctx = A816C.Data.phi_07.denote ctx :=
    A816C.Pivot.P07.fact_07 ctx hR hE_15_27 hE_16_29 hE_17_31 hE_18_33 
  have hf_08 : (Expr.var 16).denote ctx = A816C.Data.phi_08.denote ctx :=
    A816C.Pivot.P08.fact_08 ctx hR hE_15_27 hE_16_29 hE_17_31 hE_18_33 
  have hf_09 : (Expr.var 21).denote ctx = A816C.Data.phi_09.denote ctx :=
    A816C.Pivot.P09.fact_09 ctx hR hE_2_1 hE_3_3 hE_4_5 hE_5_7 hE_6_9 hE_7_11 hE_8_13 hE_9_15 hE_10_17 hE_11_19 hE_12_21 hE_13_23 hE_14_25 hE_15_27 hE_16_29 hE_17_31 hE_18_33 
  have hf_10 : (Expr.var 24).denote ctx = A816C.Data.phi_10.denote ctx :=
    A816C.Pivot.P10.fact_10 ctx hR hE_2_1 hE_3_3 hE_4_5 hE_5_7 hE_6_9 hE_7_11 hE_8_13 hE_9_15 hE_10_17 hE_11_19 hE_12_21 hE_13_23 hE_14_25 hE_15_27 hE_16_29 hE_17_31 hE_18_33 
  have hf_11 : (Expr.var 27).denote ctx = A816C.Data.phi_11.denote ctx :=
    A816C.Pivot.P11.fact_11 ctx hR hE_2_1 hE_3_3 hE_4_5 hE_5_7 hE_6_9 hE_7_11 hE_8_13 hE_9_15 hE_10_17 hE_11_19 hE_12_21 hE_13_23 hE_14_25 hE_15_27 hE_16_29 hE_17_31 hE_18_33 
  have hf_12 : (Expr.var 30).denote ctx = A816C.Data.phi_12.denote ctx :=
    A816C.Pivot.P12.fact_12 ctx hR hE_2_1 hE_3_3 hE_4_5 hE_5_7 hE_6_9 hE_7_11 hE_8_13 hE_9_15 hE_10_17 hE_11_19 hE_12_21 hE_13_23 hE_14_25 hE_15_27 hE_16_29 hE_17_31 hE_18_33 
  have hf_13 : (Expr.var 33).denote ctx = A816C.Data.phi_13.denote ctx :=
    A816C.Pivot.P13.fact_13 ctx hR hE_2_1 hE_3_3 hE_4_5 hE_5_7 hE_6_9 hE_7_11 hE_8_13 hE_9_15 hE_10_17 hE_11_19 hE_12_21 hE_13_23 hE_14_25 hE_15_27 hE_16_29 hE_17_31 hE_18_33 
  have hf_14 : (Expr.var 36).denote ctx = A816C.Data.phi_14.denote ctx :=
    A816C.Pivot.P14.fact_14 ctx hR hE_2_1 hE_3_3 hE_4_5 hE_5_7 hE_6_9 hE_7_11 hE_8_13 hE_9_15 hE_10_17 hE_11_19 hE_12_21 hE_13_23 hE_14_25 hE_15_27 hE_16_29 hE_17_31 hE_18_33 
  have hf_15 : (Expr.var 39).denote ctx = A816C.Data.phi_15.denote ctx :=
    A816C.Pivot.P15.fact_15 ctx hR hE_2_1 hE_3_3 hE_4_5 hE_5_7 hE_6_9 hE_7_11 hE_8_13 hE_9_15 hE_10_17 hE_11_19 hE_12_21 hE_13_23 hE_14_25 hE_15_27 hE_16_29 hE_17_31 hE_18_33 
  have hf_16 : (Expr.var 42).denote ctx = A816C.Data.phi_16.denote ctx :=
    A816C.Pivot.P16.fact_16 ctx hR hE_2_1 hE_3_3 hE_4_5 hE_5_7 hE_6_9 hE_7_11 hE_8_13 hE_9_15 hE_10_17 hE_11_19 hE_12_21 hE_13_23 hE_14_25 hE_15_27 hE_16_29 hE_17_31 hE_18_33 
  have hf_17 : (Expr.var 45).denote ctx = A816C.Data.phi_17.denote ctx :=
    A816C.Pivot.P17.fact_17 ctx hR hE_2_1 hE_3_3 hE_4_5 hE_5_7 hE_6_9 hE_7_11 hE_8_13 hE_9_15 hE_10_17 hE_11_19 hE_12_21 hE_13_23 hE_14_25 hE_15_27 hE_16_29 hE_17_31 hE_18_33 
  have hf_18 : (Expr.var 3).denote ctx = A816C.Data.phi_18.denote ctx :=
    A816C.Pivot.P18.fact_18 ctx hR hE_1_0 hE_2_2 hE_3_4 hE_4_6 hE_5_8 hE_6_10 hE_7_12 hE_8_14 hE_9_16 hE_10_18 hE_11_20 hE_12_22 hE_13_24 hE_14_26 hE_15_28 hE_16_30 hE_17_32 hE_18_34 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_19 : (Expr.var 5).denote ctx = A816C.Data.phi_19.denote ctx :=
    A816C.Pivot.P19.fact_19 ctx hR hE_1_0 hE_2_2 hE_3_4 hE_4_6 hE_5_8 hE_6_10 hE_7_12 hE_8_14 hE_9_16 hE_10_18 hE_11_20 hE_12_22 hE_13_24 hE_14_26 hE_15_28 hE_16_30 hE_17_32 hE_18_34 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_20 : (Expr.var 7).denote ctx = A816C.Data.phi_20.denote ctx :=
    A816C.Pivot.P20.fact_20 ctx hR hE_1_0 hE_2_2 hE_3_4 hE_4_6 hE_5_8 hE_6_10 hE_7_12 hE_8_14 hE_9_16 hE_10_18 hE_11_20 hE_12_22 hE_13_24 hE_14_26 hE_15_28 hE_16_30 hE_17_32 hE_18_34 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_21 : (Expr.var 9).denote ctx = A816C.Data.phi_21.denote ctx :=
    A816C.Pivot.P21.fact_21 ctx hR hE_1_0 hE_2_2 hE_3_4 hE_4_6 hE_5_8 hE_6_10 hE_7_12 hE_8_14 hE_9_16 hE_10_18 hE_11_20 hE_12_22 hE_13_24 hE_14_26 hE_15_28 hE_16_30 hE_17_32 hE_18_34 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_22 : (Expr.var 11).denote ctx = A816C.Data.phi_22.denote ctx :=
    A816C.Pivot.P22.fact_22 ctx hR hE_1_0 hE_2_2 hE_3_4 hE_4_6 hE_5_8 hE_6_10 hE_7_12 hE_8_14 hE_9_16 hE_10_18 hE_11_20 hE_12_22 hE_13_24 hE_14_26 hE_15_28 hE_16_30 hE_17_32 hE_18_34 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_23 : (Expr.var 13).denote ctx = A816C.Data.phi_23.denote ctx :=
    A816C.Pivot.P23.fact_23 ctx hR hE_1_0 hE_2_2 hE_3_4 hE_4_6 hE_5_8 hE_6_10 hE_7_12 hE_8_14 hE_9_16 hE_10_18 hE_11_20 hE_12_22 hE_13_24 hE_14_26 hE_15_28 hE_16_30 hE_17_32 hE_18_34 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_24 : (Expr.var 15).denote ctx = A816C.Data.phi_24.denote ctx :=
    A816C.Pivot.P24.fact_24 ctx hR hE_11_20 hE_12_22 hE_13_24 hE_14_26 hE_15_28 hE_16_30 hE_17_32 hE_18_34 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_25 : (Expr.var 19).denote ctx = A816C.Data.phi_25.denote ctx :=
    A816C.Pivot.P25.fact_25 ctx hR hE_1_0 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_26 : (Expr.var 22).denote ctx = A816C.Data.phi_26.denote ctx :=
    A816C.Pivot.P26.fact_26 ctx hR hE_1_0 hE_2_2 hE_3_4 hE_4_6 hE_5_8 hE_6_10 hE_7_12 hE_8_14 hE_9_16 hE_10_18 hE_11_20 hE_12_22 hE_13_24 hE_14_26 hE_15_28 hE_16_30 hE_17_32 hE_18_34 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_27 : (Expr.var 25).denote ctx = A816C.Data.phi_27.denote ctx :=
    A816C.Pivot.P27.fact_27 ctx hR hE_1_0 hE_2_2 hE_3_4 hE_4_6 hE_5_8 hE_6_10 hE_7_12 hE_8_14 hE_9_16 hE_10_18 hE_11_20 hE_12_22 hE_13_24 hE_14_26 hE_15_28 hE_16_30 hE_17_32 hE_18_34 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_28 : (Expr.var 28).denote ctx = A816C.Data.phi_28.denote ctx :=
    A816C.Pivot.P28.fact_28 ctx hR hE_1_0 hE_2_2 hE_3_4 hE_4_6 hE_5_8 hE_6_10 hE_7_12 hE_8_14 hE_9_16 hE_10_18 hE_11_20 hE_12_22 hE_13_24 hE_14_26 hE_15_28 hE_16_30 hE_17_32 hE_18_34 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_29 : (Expr.var 31).denote ctx = A816C.Data.phi_29.denote ctx :=
    A816C.Pivot.P29.fact_29 ctx hR hE_1_0 hE_2_2 hE_3_4 hE_4_6 hE_5_8 hE_6_10 hE_7_12 hE_8_14 hE_9_16 hE_10_18 hE_11_20 hE_12_22 hE_13_24 hE_14_26 hE_15_28 hE_16_30 hE_17_32 hE_18_34 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_30 : (Expr.var 34).denote ctx = A816C.Data.phi_30.denote ctx :=
    A816C.Pivot.P30.fact_30 ctx hR hE_1_0 hE_2_2 hE_3_4 hE_4_6 hE_5_8 hE_6_10 hE_7_12 hE_8_14 hE_9_16 hE_10_18 hE_11_20 hE_12_22 hE_13_24 hE_14_26 hE_15_28 hE_16_30 hE_17_32 hE_18_34 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_31 : (Expr.var 37).denote ctx = A816C.Data.phi_31.denote ctx :=
    A816C.Pivot.P31.fact_31 ctx hR hE_1_0 hE_2_2 hE_3_4 hE_4_6 hE_5_8 hE_6_10 hE_7_12 hE_8_14 hE_9_16 hE_10_18 hE_11_20 hE_12_22 hE_13_24 hE_14_26 hE_15_28 hE_16_30 hE_17_32 hE_18_34 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_32 : (Expr.var 40).denote ctx = A816C.Data.phi_32.denote ctx :=
    A816C.Pivot.P32.fact_32 ctx hR hE_1_0 hE_2_2 hE_3_4 hE_4_6 hE_5_8 hE_6_10 hE_7_12 hE_8_14 hE_9_16 hE_10_18 hE_11_20 hE_12_22 hE_13_24 hE_14_26 hE_15_28 hE_16_30 hE_17_32 hE_18_34 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_33 : (Expr.var 43).denote ctx = A816C.Data.phi_33.denote ctx :=
    A816C.Pivot.P33.fact_33 ctx hR hE_1_0 hE_2_2 hE_3_4 hE_4_6 hE_5_8 hE_6_10 hE_7_12 hE_8_14 hE_9_16 hE_10_18 hE_11_20 hE_12_22 hE_13_24 hE_14_26 hE_15_28 hE_16_30 hE_17_32 hE_18_34 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_34 : (Expr.var 46).denote ctx = A816C.Data.phi_34.denote ctx :=
    A816C.Pivot.P34.fact_34 ctx hR hE_1_0 hE_2_2 hE_3_4 hE_4_6 hE_5_8 hE_6_10 hE_7_12 hE_8_14 hE_9_16 hE_10_18 hE_11_20 hE_12_22 hE_13_24 hE_14_26 hE_15_28 hE_16_30 hE_17_32 hE_18_34 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_35 : (Expr.var 52).denote ctx = A816C.Data.phi_35.denote ctx :=
    A816C.Pivot.P35.fact_35 ctx hR hE_11_20 hE_12_22 hE_13_24 hE_14_26 hE_15_28 hE_16_30 hE_17_32 hE_18_34 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17
  have hf_36 : (Expr.var 20).denote ctx = A816C.Data.phi_36.denote ctx :=
    A816C.Pivot.P36.fact_36 ctx hR hE_1_1 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31 hf_32 hf_33 hf_34 hf_35
  have hf_37 : (Expr.var 23).denote ctx = A816C.Data.phi_37.denote ctx :=
    A816C.Pivot.P37.fact_37 ctx hR hE_1_1 hE_2_3 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31 hf_32 hf_33 hf_34 hf_35
  have hf_38 : (Expr.var 26).denote ctx = A816C.Data.phi_38.denote ctx :=
    A816C.Pivot.P38.fact_38 ctx hR hE_1_1 hE_2_3 hE_3_5 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31 hf_32 hf_33 hf_34 hf_35
  have hf_39 : (Expr.var 29).denote ctx = A816C.Data.phi_39.denote ctx :=
    A816C.Pivot.P39.fact_39 ctx hR hE_1_1 hE_2_3 hE_3_5 hE_4_7 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31 hf_32 hf_33 hf_34 hf_35
  have hf_40 : (Expr.var 32).denote ctx = A816C.Data.phi_40.denote ctx :=
    A816C.Pivot.P40.fact_40 ctx hR hE_1_1 hE_2_3 hE_3_5 hE_4_7 hE_5_9 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31 hf_32 hf_33 hf_34 hf_35
  have hf_41 : (Expr.var 35).denote ctx = A816C.Data.phi_41.denote ctx :=
    A816C.Pivot.P41.fact_41 ctx hR hE_1_1 hE_2_3 hE_3_5 hE_4_7 hE_5_9 hE_6_11 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31 hf_32 hf_33 hf_34 hf_35
  have hf_42 : (Expr.var 38).denote ctx = A816C.Data.phi_42.denote ctx :=
    A816C.Pivot.P42.fact_42 ctx hR hE_1_1 hE_2_3 hE_3_5 hE_4_7 hE_5_9 hE_6_11 hE_7_13 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31 hf_32 hf_33 hf_34 hf_35
  have hf_43 : (Expr.var 41).denote ctx = A816C.Data.phi_43.denote ctx :=
    A816C.Pivot.P43.fact_43 ctx hR hE_1_1 hE_2_3 hE_3_5 hE_4_7 hE_5_9 hE_6_11 hE_7_13 hE_8_15 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31 hf_32 hf_33 hf_34 hf_35
  have hf_44 : (Expr.var 44).denote ctx = A816C.Data.phi_44.denote ctx :=
    A816C.Pivot.P44.fact_44 ctx hR hE_1_1 hE_2_3 hE_3_5 hE_4_7 hE_5_9 hE_6_11 hE_7_13 hE_8_15 hE_9_17 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31 hf_32 hf_33 hf_34 hf_35
  have hf_45 : (Expr.var 47).denote ctx = A816C.Data.phi_45.denote ctx :=
    A816C.Pivot.P45.fact_45 ctx hR hE_1_1 hE_2_3 hE_3_5 hE_4_7 hE_5_9 hE_6_11 hE_7_13 hE_8_15 hE_9_17 hE_10_19 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31 hf_32 hf_33 hf_34 hf_35
  have hf_46 : (Expr.var 50).denote ctx = A816C.Data.phi_46.denote ctx :=
    A816C.Pivot.P46.fact_46 ctx hR hE_1_1 hE_2_3 hE_3_5 hE_4_7 hE_5_9 hE_6_11 hE_7_13 hE_8_15 hE_9_17 hE_10_19 hE_11_21 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31 hf_32 hf_33 hf_34 hf_35
  have hf_47 : (Expr.var 53).denote ctx = A816C.Data.phi_47.denote ctx :=
    A816C.Pivot.P47.fact_47 ctx hR hE_1_1 hE_2_3 hE_3_5 hE_4_7 hE_5_9 hE_6_11 hE_7_13 hE_8_15 hE_9_17 hE_10_19 hE_11_21 hE_12_23 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31 hf_32 hf_33 hf_34 hf_35
  exact A816C.Final.a816_zero ctx hR hE_13_25 hE_14_27 hE_15_29 hE_16_31 hE_17_33 hE_18_35 hE_2_4 hE_3_6 hE_4_8 hf_01 hf_02 hf_03 hf_04 hf_05 hf_06 hf_07 hf_08 hf_09 hf_10 hf_11 hf_12 hf_13 hf_14 hf_15 hf_16 hf_17 hf_18 hf_19 hf_20 hf_21 hf_22 hf_23 hf_24 hf_25 hf_26 hf_27 hf_28 hf_29 hf_30 hf_31 hf_32 hf_33 hf_34 hf_35 hf_36 hf_37 hf_38 hf_39 hf_40 hf_41 hf_42 hf_43 hf_44 hf_45 hf_46 hf_47

end A816C
