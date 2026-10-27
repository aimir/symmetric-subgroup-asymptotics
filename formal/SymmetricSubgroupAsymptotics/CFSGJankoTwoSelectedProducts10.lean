import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedPositiveWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches09
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts09
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches06
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedSeedPowerPilot
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches10
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts10
open MatrixKroneckerProductReflection
open CFSGJankoTwoSelectedPositiveWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check087_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C086_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C087_digit 0 j%5 := by decide +kernel

private theorem check087_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C086_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C087_digit 1 j%5 := by decide +kernel

private theorem check087_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C086_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C087_digit 2 j%5 := by decide +kernel

private theorem check087_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C086_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C087_digit 3 j%5 := by decide +kernel

private theorem check087_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C086_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C087_digit 4 j%5 := by decide +kernel

private theorem check087_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C086_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C087_digit 5 j%5 := by decide +kernel

private theorem check087_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C086_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C087_digit 6 j%5 := by decide +kernel

private theorem check087_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C086_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C087_digit 7 j%5 := by decide +kernel

private theorem check087_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C086_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C087_digit 8 j%5 := by decide +kernel

private theorem check087_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C086_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C087_digit 9 j%5 := by decide +kernel

private theorem check087_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C086_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C087_digit 10 j%5 := by decide +kernel

private theorem check087_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C086_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C087_digit 11 j%5 := by decide +kernel

private theorem check087_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C086_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C087_digit 12 j%5 := by decide +kernel

private theorem check087_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C086_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C087_digit 13 j%5 := by decide +kernel

theorem checks087 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C086_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C087_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check087_00 j
  · exact check087_01 j
  · exact check087_02 j
  · exact check087_03 j
  · exact check087_04 j
  · exact check087_05 j
  · exact check087_06 j
  · exact check087_07 j
  · exact check087_08 j
  · exact check087_09 j
  · exact check087_10 j
  · exact check087_11 j
  · exact check087_12 j
  · exact check087_13 j

theorem matrix_node087 : (node087 A B)=CFSGJankoTwoSelectedCaches09.C087_data.matrix 5 := by
  change (node086 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches09.C086_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches09.C087_data
    CFSGJankoTwoSelectedProducts09.matrix_node086 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks087

private theorem check088_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C087_rowCode 0*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C088_digit 0 j%5 := by decide +kernel

private theorem check088_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C087_rowCode 1*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C088_digit 1 j%5 := by decide +kernel

private theorem check088_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C087_rowCode 2*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C088_digit 2 j%5 := by decide +kernel

private theorem check088_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C087_rowCode 3*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C088_digit 3 j%5 := by decide +kernel

private theorem check088_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C087_rowCode 4*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C088_digit 4 j%5 := by decide +kernel

private theorem check088_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C087_rowCode 5*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C088_digit 5 j%5 := by decide +kernel

private theorem check088_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C087_rowCode 6*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C088_digit 6 j%5 := by decide +kernel

private theorem check088_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C087_rowCode 7*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C088_digit 7 j%5 := by decide +kernel

private theorem check088_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C087_rowCode 8*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C088_digit 8 j%5 := by decide +kernel

private theorem check088_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C087_rowCode 9*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C088_digit 9 j%5 := by decide +kernel

private theorem check088_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C087_rowCode 10*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C088_digit 10 j%5 := by decide +kernel

private theorem check088_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C087_rowCode 11*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C088_digit 11 j%5 := by decide +kernel

private theorem check088_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C087_rowCode 12*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C088_digit 12 j%5 := by decide +kernel

private theorem check088_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C087_rowCode 13*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C088_digit 13 j%5 := by decide +kernel

theorem checks088 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C087_rowCode i*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C088_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check088_00 j
  · exact check088_01 j
  · exact check088_02 j
  · exact check088_03 j
  · exact check088_04 j
  · exact check088_05 j
  · exact check088_06 j
  · exact check088_07 j
  · exact check088_08 j
  · exact check088_09 j
  · exact check088_10 j
  · exact check088_11 j
  · exact check088_12 j
  · exact check088_13 j

theorem matrix_node088 : (node088 A B)=CFSGJankoTwoSelectedCaches09.C088_data.matrix 5 := by
  change (node087 A B)*(node059 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches09.C087_data CFSGJankoTwoSelectedCaches06.C059_data CFSGJankoTwoSelectedCaches09.C088_data
    CFSGJankoTwoSelectedProducts10.matrix_node087 CFSGJankoTwoSelectedSeedPowerPilot.matrix_node059 (by decide : 14*(5-1)^2 < 256) checks088

private theorem check089_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C088_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C089_digit 0 j%5 := by decide +kernel

private theorem check089_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C088_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C089_digit 1 j%5 := by decide +kernel

private theorem check089_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C088_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C089_digit 2 j%5 := by decide +kernel

private theorem check089_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C088_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C089_digit 3 j%5 := by decide +kernel

private theorem check089_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C088_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C089_digit 4 j%5 := by decide +kernel

private theorem check089_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C088_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C089_digit 5 j%5 := by decide +kernel

private theorem check089_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C088_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C089_digit 6 j%5 := by decide +kernel

private theorem check089_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C088_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C089_digit 7 j%5 := by decide +kernel

private theorem check089_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C088_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C089_digit 8 j%5 := by decide +kernel

private theorem check089_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C088_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C089_digit 9 j%5 := by decide +kernel

private theorem check089_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C088_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C089_digit 10 j%5 := by decide +kernel

private theorem check089_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C088_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C089_digit 11 j%5 := by decide +kernel

private theorem check089_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C088_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C089_digit 12 j%5 := by decide +kernel

private theorem check089_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C088_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C089_digit 13 j%5 := by decide +kernel

theorem checks089 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C088_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C089_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check089_00 j
  · exact check089_01 j
  · exact check089_02 j
  · exact check089_03 j
  · exact check089_04 j
  · exact check089_05 j
  · exact check089_06 j
  · exact check089_07 j
  · exact check089_08 j
  · exact check089_09 j
  · exact check089_10 j
  · exact check089_11 j
  · exact check089_12 j
  · exact check089_13 j

theorem matrix_node089 : (node089 A B)=CFSGJankoTwoSelectedCaches10.C089_data.matrix 5 := by
  change (node088 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches09.C088_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches10.C089_data
    CFSGJankoTwoSelectedProducts10.matrix_node088 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks089

private theorem check090_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C089_rowCode 0*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C090_digit 0 j%5 := by decide +kernel

private theorem check090_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C089_rowCode 1*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C090_digit 1 j%5 := by decide +kernel

private theorem check090_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C089_rowCode 2*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C090_digit 2 j%5 := by decide +kernel

private theorem check090_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C089_rowCode 3*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C090_digit 3 j%5 := by decide +kernel

private theorem check090_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C089_rowCode 4*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C090_digit 4 j%5 := by decide +kernel

private theorem check090_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C089_rowCode 5*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C090_digit 5 j%5 := by decide +kernel

private theorem check090_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C089_rowCode 6*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C090_digit 6 j%5 := by decide +kernel

private theorem check090_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C089_rowCode 7*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C090_digit 7 j%5 := by decide +kernel

private theorem check090_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C089_rowCode 8*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C090_digit 8 j%5 := by decide +kernel

private theorem check090_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C089_rowCode 9*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C090_digit 9 j%5 := by decide +kernel

private theorem check090_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C089_rowCode 10*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C090_digit 10 j%5 := by decide +kernel

private theorem check090_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C089_rowCode 11*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C090_digit 11 j%5 := by decide +kernel

private theorem check090_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C089_rowCode 12*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C090_digit 12 j%5 := by decide +kernel

private theorem check090_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C089_rowCode 13*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C090_digit 13 j%5 := by decide +kernel

theorem checks090 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C089_rowCode i*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C090_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check090_00 j
  · exact check090_01 j
  · exact check090_02 j
  · exact check090_03 j
  · exact check090_04 j
  · exact check090_05 j
  · exact check090_06 j
  · exact check090_07 j
  · exact check090_08 j
  · exact check090_09 j
  · exact check090_10 j
  · exact check090_11 j
  · exact check090_12 j
  · exact check090_13 j

theorem matrix_node090 : (node090 A B)=CFSGJankoTwoSelectedCaches10.C090_data.matrix 5 := by
  change (node089 A B)*(node059 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches10.C089_data CFSGJankoTwoSelectedCaches06.C059_data CFSGJankoTwoSelectedCaches10.C090_data
    CFSGJankoTwoSelectedProducts10.matrix_node089 CFSGJankoTwoSelectedSeedPowerPilot.matrix_node059 (by decide : 14*(5-1)^2 < 256) checks090

private theorem check091_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C090_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C091_digit 0 j%5 := by decide +kernel

private theorem check091_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C090_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C091_digit 1 j%5 := by decide +kernel

private theorem check091_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C090_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C091_digit 2 j%5 := by decide +kernel

private theorem check091_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C090_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C091_digit 3 j%5 := by decide +kernel

private theorem check091_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C090_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C091_digit 4 j%5 := by decide +kernel

private theorem check091_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C090_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C091_digit 5 j%5 := by decide +kernel

private theorem check091_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C090_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C091_digit 6 j%5 := by decide +kernel

private theorem check091_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C090_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C091_digit 7 j%5 := by decide +kernel

private theorem check091_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C090_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C091_digit 8 j%5 := by decide +kernel

private theorem check091_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C090_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C091_digit 9 j%5 := by decide +kernel

private theorem check091_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C090_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C091_digit 10 j%5 := by decide +kernel

private theorem check091_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C090_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C091_digit 11 j%5 := by decide +kernel

private theorem check091_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C090_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C091_digit 12 j%5 := by decide +kernel

private theorem check091_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C090_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C091_digit 13 j%5 := by decide +kernel

theorem checks091 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C090_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C091_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check091_00 j
  · exact check091_01 j
  · exact check091_02 j
  · exact check091_03 j
  · exact check091_04 j
  · exact check091_05 j
  · exact check091_06 j
  · exact check091_07 j
  · exact check091_08 j
  · exact check091_09 j
  · exact check091_10 j
  · exact check091_11 j
  · exact check091_12 j
  · exact check091_13 j

theorem matrix_node091 : (node091 A B)=CFSGJankoTwoSelectedCaches10.C091_data.matrix 5 := by
  change (node090 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches10.C090_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches10.C091_data
    CFSGJankoTwoSelectedProducts10.matrix_node090 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks091

private theorem check092_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C091_rowCode 0*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C092_digit 0 j%5 := by decide +kernel

private theorem check092_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C091_rowCode 1*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C092_digit 1 j%5 := by decide +kernel

private theorem check092_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C091_rowCode 2*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C092_digit 2 j%5 := by decide +kernel

private theorem check092_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C091_rowCode 3*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C092_digit 3 j%5 := by decide +kernel

private theorem check092_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C091_rowCode 4*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C092_digit 4 j%5 := by decide +kernel

private theorem check092_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C091_rowCode 5*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C092_digit 5 j%5 := by decide +kernel

private theorem check092_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C091_rowCode 6*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C092_digit 6 j%5 := by decide +kernel

private theorem check092_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C091_rowCode 7*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C092_digit 7 j%5 := by decide +kernel

private theorem check092_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C091_rowCode 8*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C092_digit 8 j%5 := by decide +kernel

private theorem check092_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C091_rowCode 9*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C092_digit 9 j%5 := by decide +kernel

private theorem check092_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C091_rowCode 10*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C092_digit 10 j%5 := by decide +kernel

private theorem check092_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C091_rowCode 11*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C092_digit 11 j%5 := by decide +kernel

private theorem check092_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C091_rowCode 12*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C092_digit 12 j%5 := by decide +kernel

private theorem check092_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C091_rowCode 13*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C092_digit 13 j%5 := by decide +kernel

theorem checks092 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C091_rowCode i*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C092_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check092_00 j
  · exact check092_01 j
  · exact check092_02 j
  · exact check092_03 j
  · exact check092_04 j
  · exact check092_05 j
  · exact check092_06 j
  · exact check092_07 j
  · exact check092_08 j
  · exact check092_09 j
  · exact check092_10 j
  · exact check092_11 j
  · exact check092_12 j
  · exact check092_13 j

theorem matrix_node092 : (node092 A B)=CFSGJankoTwoSelectedCaches10.C092_data.matrix 5 := by
  change (node091 A B)*(node001 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches10.C091_data CFSGJankoTwoSelectedBaseCaches.B_data CFSGJankoTwoSelectedCaches10.C092_data
    CFSGJankoTwoSelectedProducts10.matrix_node091 CFSGJankoTwoSelectedBaseCaches.B_source_binding (by decide : 14*(5-1)^2 < 256) checks092

private theorem check093_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C092_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C093_digit 0 j%5 := by decide +kernel

private theorem check093_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C092_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C093_digit 1 j%5 := by decide +kernel

private theorem check093_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C092_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C093_digit 2 j%5 := by decide +kernel

private theorem check093_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C092_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C093_digit 3 j%5 := by decide +kernel

private theorem check093_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C092_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C093_digit 4 j%5 := by decide +kernel

private theorem check093_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C092_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C093_digit 5 j%5 := by decide +kernel

private theorem check093_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C092_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C093_digit 6 j%5 := by decide +kernel

private theorem check093_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C092_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C093_digit 7 j%5 := by decide +kernel

private theorem check093_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C092_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C093_digit 8 j%5 := by decide +kernel

private theorem check093_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C092_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C093_digit 9 j%5 := by decide +kernel

private theorem check093_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C092_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C093_digit 10 j%5 := by decide +kernel

private theorem check093_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C092_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C093_digit 11 j%5 := by decide +kernel

private theorem check093_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C092_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C093_digit 12 j%5 := by decide +kernel

private theorem check093_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C092_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C093_digit 13 j%5 := by decide +kernel

theorem checks093 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C092_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C093_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check093_00 j
  · exact check093_01 j
  · exact check093_02 j
  · exact check093_03 j
  · exact check093_04 j
  · exact check093_05 j
  · exact check093_06 j
  · exact check093_07 j
  · exact check093_08 j
  · exact check093_09 j
  · exact check093_10 j
  · exact check093_11 j
  · exact check093_12 j
  · exact check093_13 j

theorem matrix_node093 : (node093 A B)=CFSGJankoTwoSelectedCaches10.C093_data.matrix 5 := by
  change (node092 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches10.C092_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches10.C093_data
    CFSGJankoTwoSelectedProducts10.matrix_node092 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks093

private theorem check094_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C093_rowCode 0*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 0 j%5 := by decide +kernel

private theorem check094_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C093_rowCode 1*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 1 j%5 := by decide +kernel

private theorem check094_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C093_rowCode 2*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 2 j%5 := by decide +kernel

private theorem check094_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C093_rowCode 3*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 3 j%5 := by decide +kernel

private theorem check094_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C093_rowCode 4*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 4 j%5 := by decide +kernel

private theorem check094_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C093_rowCode 5*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 5 j%5 := by decide +kernel

private theorem check094_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C093_rowCode 6*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 6 j%5 := by decide +kernel

private theorem check094_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C093_rowCode 7*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 7 j%5 := by decide +kernel

private theorem check094_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C093_rowCode 8*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 8 j%5 := by decide +kernel

private theorem check094_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C093_rowCode 9*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 9 j%5 := by decide +kernel

private theorem check094_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C093_rowCode 10*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 10 j%5 := by decide +kernel

private theorem check094_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C093_rowCode 11*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 11 j%5 := by decide +kernel

private theorem check094_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C093_rowCode 12*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 12 j%5 := by decide +kernel

private theorem check094_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C093_rowCode 13*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 13 j%5 := by decide +kernel

theorem checks094 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C093_rowCode i*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check094_00 j
  · exact check094_01 j
  · exact check094_02 j
  · exact check094_03 j
  · exact check094_04 j
  · exact check094_05 j
  · exact check094_06 j
  · exact check094_07 j
  · exact check094_08 j
  · exact check094_09 j
  · exact check094_10 j
  · exact check094_11 j
  · exact check094_12 j
  · exact check094_13 j

theorem matrix_node094 : (node094 A B)=CFSGJankoTwoSelectedCaches10.C094_data.matrix 5 := by
  change (node093 A B)*(node059 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches10.C093_data CFSGJankoTwoSelectedCaches06.C059_data CFSGJankoTwoSelectedCaches10.C094_data
    CFSGJankoTwoSelectedProducts10.matrix_node093 CFSGJankoTwoSelectedSeedPowerPilot.matrix_node059 (by decide : 14*(5-1)^2 < 256) checks094

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts10
