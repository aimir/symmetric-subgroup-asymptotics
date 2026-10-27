import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedPositiveWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches08
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts08
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches06
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedSeedPowerPilot
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches09
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts09
open MatrixKroneckerProductReflection
open CFSGJankoTwoSelectedPositiveWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check079_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C078_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C079_digit 0 j%5 := by decide +kernel

private theorem check079_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C078_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C079_digit 1 j%5 := by decide +kernel

private theorem check079_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C078_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C079_digit 2 j%5 := by decide +kernel

private theorem check079_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C078_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C079_digit 3 j%5 := by decide +kernel

private theorem check079_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C078_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C079_digit 4 j%5 := by decide +kernel

private theorem check079_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C078_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C079_digit 5 j%5 := by decide +kernel

private theorem check079_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C078_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C079_digit 6 j%5 := by decide +kernel

private theorem check079_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C078_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C079_digit 7 j%5 := by decide +kernel

private theorem check079_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C078_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C079_digit 8 j%5 := by decide +kernel

private theorem check079_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C078_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C079_digit 9 j%5 := by decide +kernel

private theorem check079_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C078_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C079_digit 10 j%5 := by decide +kernel

private theorem check079_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C078_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C079_digit 11 j%5 := by decide +kernel

private theorem check079_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C078_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C079_digit 12 j%5 := by decide +kernel

private theorem check079_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C078_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C079_digit 13 j%5 := by decide +kernel

theorem checks079 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C078_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C079_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check079_00 j
  · exact check079_01 j
  · exact check079_02 j
  · exact check079_03 j
  · exact check079_04 j
  · exact check079_05 j
  · exact check079_06 j
  · exact check079_07 j
  · exact check079_08 j
  · exact check079_09 j
  · exact check079_10 j
  · exact check079_11 j
  · exact check079_12 j
  · exact check079_13 j

theorem matrix_node079 : (node079 A B)=CFSGJankoTwoSelectedCaches08.C079_data.matrix 5 := by
  change (node078 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches08.C078_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches08.C079_data
    CFSGJankoTwoSelectedProducts08.matrix_node078 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks079

private theorem check080_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C079_rowCode 0*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C080_digit 0 j%5 := by decide +kernel

private theorem check080_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C079_rowCode 1*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C080_digit 1 j%5 := by decide +kernel

private theorem check080_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C079_rowCode 2*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C080_digit 2 j%5 := by decide +kernel

private theorem check080_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C079_rowCode 3*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C080_digit 3 j%5 := by decide +kernel

private theorem check080_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C079_rowCode 4*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C080_digit 4 j%5 := by decide +kernel

private theorem check080_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C079_rowCode 5*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C080_digit 5 j%5 := by decide +kernel

private theorem check080_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C079_rowCode 6*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C080_digit 6 j%5 := by decide +kernel

private theorem check080_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C079_rowCode 7*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C080_digit 7 j%5 := by decide +kernel

private theorem check080_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C079_rowCode 8*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C080_digit 8 j%5 := by decide +kernel

private theorem check080_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C079_rowCode 9*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C080_digit 9 j%5 := by decide +kernel

private theorem check080_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C079_rowCode 10*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C080_digit 10 j%5 := by decide +kernel

private theorem check080_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C079_rowCode 11*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C080_digit 11 j%5 := by decide +kernel

private theorem check080_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C079_rowCode 12*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C080_digit 12 j%5 := by decide +kernel

private theorem check080_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C079_rowCode 13*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C080_digit 13 j%5 := by decide +kernel

theorem checks080 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C079_rowCode i*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C080_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check080_00 j
  · exact check080_01 j
  · exact check080_02 j
  · exact check080_03 j
  · exact check080_04 j
  · exact check080_05 j
  · exact check080_06 j
  · exact check080_07 j
  · exact check080_08 j
  · exact check080_09 j
  · exact check080_10 j
  · exact check080_11 j
  · exact check080_12 j
  · exact check080_13 j

theorem matrix_node080 : (node080 A B)=CFSGJankoTwoSelectedCaches08.C080_data.matrix 5 := by
  change (node079 A B)*(node059 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches08.C079_data CFSGJankoTwoSelectedCaches06.C059_data CFSGJankoTwoSelectedCaches08.C080_data
    CFSGJankoTwoSelectedProducts09.matrix_node079 CFSGJankoTwoSelectedSeedPowerPilot.matrix_node059 (by decide : 14*(5-1)^2 < 256) checks080

private theorem check081_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C080_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C081_digit 0 j%5 := by decide +kernel

private theorem check081_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C080_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C081_digit 1 j%5 := by decide +kernel

private theorem check081_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C080_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C081_digit 2 j%5 := by decide +kernel

private theorem check081_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C080_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C081_digit 3 j%5 := by decide +kernel

private theorem check081_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C080_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C081_digit 4 j%5 := by decide +kernel

private theorem check081_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C080_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C081_digit 5 j%5 := by decide +kernel

private theorem check081_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C080_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C081_digit 6 j%5 := by decide +kernel

private theorem check081_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C080_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C081_digit 7 j%5 := by decide +kernel

private theorem check081_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C080_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C081_digit 8 j%5 := by decide +kernel

private theorem check081_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C080_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C081_digit 9 j%5 := by decide +kernel

private theorem check081_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C080_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C081_digit 10 j%5 := by decide +kernel

private theorem check081_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C080_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C081_digit 11 j%5 := by decide +kernel

private theorem check081_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C080_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C081_digit 12 j%5 := by decide +kernel

private theorem check081_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C080_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C081_digit 13 j%5 := by decide +kernel

theorem checks081 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C080_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C081_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check081_00 j
  · exact check081_01 j
  · exact check081_02 j
  · exact check081_03 j
  · exact check081_04 j
  · exact check081_05 j
  · exact check081_06 j
  · exact check081_07 j
  · exact check081_08 j
  · exact check081_09 j
  · exact check081_10 j
  · exact check081_11 j
  · exact check081_12 j
  · exact check081_13 j

theorem matrix_node081 : (node081 A B)=CFSGJankoTwoSelectedCaches08.C081_data.matrix 5 := by
  change (node080 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches08.C080_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches08.C081_data
    CFSGJankoTwoSelectedProducts09.matrix_node080 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks081

private theorem check082_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C081_rowCode 0*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C082_digit 0 j%5 := by decide +kernel

private theorem check082_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C081_rowCode 1*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C082_digit 1 j%5 := by decide +kernel

private theorem check082_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C081_rowCode 2*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C082_digit 2 j%5 := by decide +kernel

private theorem check082_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C081_rowCode 3*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C082_digit 3 j%5 := by decide +kernel

private theorem check082_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C081_rowCode 4*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C082_digit 4 j%5 := by decide +kernel

private theorem check082_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C081_rowCode 5*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C082_digit 5 j%5 := by decide +kernel

private theorem check082_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C081_rowCode 6*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C082_digit 6 j%5 := by decide +kernel

private theorem check082_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C081_rowCode 7*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C082_digit 7 j%5 := by decide +kernel

private theorem check082_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C081_rowCode 8*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C082_digit 8 j%5 := by decide +kernel

private theorem check082_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C081_rowCode 9*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C082_digit 9 j%5 := by decide +kernel

private theorem check082_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C081_rowCode 10*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C082_digit 10 j%5 := by decide +kernel

private theorem check082_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C081_rowCode 11*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C082_digit 11 j%5 := by decide +kernel

private theorem check082_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C081_rowCode 12*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C082_digit 12 j%5 := by decide +kernel

private theorem check082_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C081_rowCode 13*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C082_digit 13 j%5 := by decide +kernel

theorem checks082 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C081_rowCode i*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C082_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check082_00 j
  · exact check082_01 j
  · exact check082_02 j
  · exact check082_03 j
  · exact check082_04 j
  · exact check082_05 j
  · exact check082_06 j
  · exact check082_07 j
  · exact check082_08 j
  · exact check082_09 j
  · exact check082_10 j
  · exact check082_11 j
  · exact check082_12 j
  · exact check082_13 j

theorem matrix_node082 : (node082 A B)=CFSGJankoTwoSelectedCaches08.C082_data.matrix 5 := by
  change (node081 A B)*(node059 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches08.C081_data CFSGJankoTwoSelectedCaches06.C059_data CFSGJankoTwoSelectedCaches08.C082_data
    CFSGJankoTwoSelectedProducts09.matrix_node081 CFSGJankoTwoSelectedSeedPowerPilot.matrix_node059 (by decide : 14*(5-1)^2 < 256) checks082

private theorem check083_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C082_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C083_digit 0 j%5 := by decide +kernel

private theorem check083_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C082_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C083_digit 1 j%5 := by decide +kernel

private theorem check083_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C082_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C083_digit 2 j%5 := by decide +kernel

private theorem check083_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C082_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C083_digit 3 j%5 := by decide +kernel

private theorem check083_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C082_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C083_digit 4 j%5 := by decide +kernel

private theorem check083_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C082_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C083_digit 5 j%5 := by decide +kernel

private theorem check083_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C082_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C083_digit 6 j%5 := by decide +kernel

private theorem check083_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C082_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C083_digit 7 j%5 := by decide +kernel

private theorem check083_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C082_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C083_digit 8 j%5 := by decide +kernel

private theorem check083_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C082_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C083_digit 9 j%5 := by decide +kernel

private theorem check083_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C082_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C083_digit 10 j%5 := by decide +kernel

private theorem check083_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C082_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C083_digit 11 j%5 := by decide +kernel

private theorem check083_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C082_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C083_digit 12 j%5 := by decide +kernel

private theorem check083_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C082_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C083_digit 13 j%5 := by decide +kernel

theorem checks083 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C082_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C083_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check083_00 j
  · exact check083_01 j
  · exact check083_02 j
  · exact check083_03 j
  · exact check083_04 j
  · exact check083_05 j
  · exact check083_06 j
  · exact check083_07 j
  · exact check083_08 j
  · exact check083_09 j
  · exact check083_10 j
  · exact check083_11 j
  · exact check083_12 j
  · exact check083_13 j

theorem matrix_node083 : (node083 A B)=CFSGJankoTwoSelectedCaches09.C083_data.matrix 5 := by
  change (node082 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches08.C082_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches09.C083_data
    CFSGJankoTwoSelectedProducts09.matrix_node082 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks083

private theorem check084_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C083_rowCode 0*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C084_digit 0 j%5 := by decide +kernel

private theorem check084_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C083_rowCode 1*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C084_digit 1 j%5 := by decide +kernel

private theorem check084_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C083_rowCode 2*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C084_digit 2 j%5 := by decide +kernel

private theorem check084_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C083_rowCode 3*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C084_digit 3 j%5 := by decide +kernel

private theorem check084_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C083_rowCode 4*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C084_digit 4 j%5 := by decide +kernel

private theorem check084_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C083_rowCode 5*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C084_digit 5 j%5 := by decide +kernel

private theorem check084_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C083_rowCode 6*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C084_digit 6 j%5 := by decide +kernel

private theorem check084_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C083_rowCode 7*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C084_digit 7 j%5 := by decide +kernel

private theorem check084_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C083_rowCode 8*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C084_digit 8 j%5 := by decide +kernel

private theorem check084_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C083_rowCode 9*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C084_digit 9 j%5 := by decide +kernel

private theorem check084_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C083_rowCode 10*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C084_digit 10 j%5 := by decide +kernel

private theorem check084_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C083_rowCode 11*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C084_digit 11 j%5 := by decide +kernel

private theorem check084_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C083_rowCode 12*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C084_digit 12 j%5 := by decide +kernel

private theorem check084_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C083_rowCode 13*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C084_digit 13 j%5 := by decide +kernel

theorem checks084 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C083_rowCode i*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C084_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check084_00 j
  · exact check084_01 j
  · exact check084_02 j
  · exact check084_03 j
  · exact check084_04 j
  · exact check084_05 j
  · exact check084_06 j
  · exact check084_07 j
  · exact check084_08 j
  · exact check084_09 j
  · exact check084_10 j
  · exact check084_11 j
  · exact check084_12 j
  · exact check084_13 j

theorem matrix_node084 : (node084 A B)=CFSGJankoTwoSelectedCaches09.C084_data.matrix 5 := by
  change (node083 A B)*(node001 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches09.C083_data CFSGJankoTwoSelectedBaseCaches.B_data CFSGJankoTwoSelectedCaches09.C084_data
    CFSGJankoTwoSelectedProducts09.matrix_node083 CFSGJankoTwoSelectedBaseCaches.B_source_binding (by decide : 14*(5-1)^2 < 256) checks084

private theorem check085_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C084_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C085_digit 0 j%5 := by decide +kernel

private theorem check085_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C084_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C085_digit 1 j%5 := by decide +kernel

private theorem check085_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C084_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C085_digit 2 j%5 := by decide +kernel

private theorem check085_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C084_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C085_digit 3 j%5 := by decide +kernel

private theorem check085_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C084_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C085_digit 4 j%5 := by decide +kernel

private theorem check085_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C084_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C085_digit 5 j%5 := by decide +kernel

private theorem check085_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C084_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C085_digit 6 j%5 := by decide +kernel

private theorem check085_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C084_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C085_digit 7 j%5 := by decide +kernel

private theorem check085_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C084_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C085_digit 8 j%5 := by decide +kernel

private theorem check085_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C084_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C085_digit 9 j%5 := by decide +kernel

private theorem check085_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C084_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C085_digit 10 j%5 := by decide +kernel

private theorem check085_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C084_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C085_digit 11 j%5 := by decide +kernel

private theorem check085_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C084_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C085_digit 12 j%5 := by decide +kernel

private theorem check085_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C084_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C085_digit 13 j%5 := by decide +kernel

theorem checks085 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C084_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C085_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check085_00 j
  · exact check085_01 j
  · exact check085_02 j
  · exact check085_03 j
  · exact check085_04 j
  · exact check085_05 j
  · exact check085_06 j
  · exact check085_07 j
  · exact check085_08 j
  · exact check085_09 j
  · exact check085_10 j
  · exact check085_11 j
  · exact check085_12 j
  · exact check085_13 j

theorem matrix_node085 : (node085 A B)=CFSGJankoTwoSelectedCaches09.C085_data.matrix 5 := by
  change (node084 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches09.C084_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches09.C085_data
    CFSGJankoTwoSelectedProducts09.matrix_node084 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks085

private theorem check086_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C085_rowCode 0*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C086_digit 0 j%5 := by decide +kernel

private theorem check086_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C085_rowCode 1*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C086_digit 1 j%5 := by decide +kernel

private theorem check086_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C085_rowCode 2*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C086_digit 2 j%5 := by decide +kernel

private theorem check086_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C085_rowCode 3*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C086_digit 3 j%5 := by decide +kernel

private theorem check086_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C085_rowCode 4*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C086_digit 4 j%5 := by decide +kernel

private theorem check086_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C085_rowCode 5*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C086_digit 5 j%5 := by decide +kernel

private theorem check086_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C085_rowCode 6*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C086_digit 6 j%5 := by decide +kernel

private theorem check086_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C085_rowCode 7*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C086_digit 7 j%5 := by decide +kernel

private theorem check086_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C085_rowCode 8*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C086_digit 8 j%5 := by decide +kernel

private theorem check086_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C085_rowCode 9*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C086_digit 9 j%5 := by decide +kernel

private theorem check086_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C085_rowCode 10*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C086_digit 10 j%5 := by decide +kernel

private theorem check086_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C085_rowCode 11*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C086_digit 11 j%5 := by decide +kernel

private theorem check086_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C085_rowCode 12*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C086_digit 12 j%5 := by decide +kernel

private theorem check086_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C085_rowCode 13*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C086_digit 13 j%5 := by decide +kernel

theorem checks086 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches09.C085_rowCode i*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches09.C086_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check086_00 j
  · exact check086_01 j
  · exact check086_02 j
  · exact check086_03 j
  · exact check086_04 j
  · exact check086_05 j
  · exact check086_06 j
  · exact check086_07 j
  · exact check086_08 j
  · exact check086_09 j
  · exact check086_10 j
  · exact check086_11 j
  · exact check086_12 j
  · exact check086_13 j

theorem matrix_node086 : (node086 A B)=CFSGJankoTwoSelectedCaches09.C086_data.matrix 5 := by
  change (node085 A B)*(node001 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches09.C085_data CFSGJankoTwoSelectedBaseCaches.B_data CFSGJankoTwoSelectedCaches09.C086_data
    CFSGJankoTwoSelectedProducts09.matrix_node085 CFSGJankoTwoSelectedBaseCaches.B_source_binding (by decide : 14*(5-1)^2 < 256) checks086

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts09
