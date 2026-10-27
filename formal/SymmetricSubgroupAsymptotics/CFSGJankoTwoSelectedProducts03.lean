import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedPositiveWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches03
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches04
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts02
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches02
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts01
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches05
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts03
open MatrixKroneckerProductReflection
open CFSGJankoTwoSelectedPositiveWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check027_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C026_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C027_digit 0 j%5 := by decide +kernel

private theorem check027_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C026_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C027_digit 1 j%5 := by decide +kernel

private theorem check027_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C026_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C027_digit 2 j%5 := by decide +kernel

private theorem check027_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C026_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C027_digit 3 j%5 := by decide +kernel

private theorem check027_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C026_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C027_digit 4 j%5 := by decide +kernel

private theorem check027_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C026_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C027_digit 5 j%5 := by decide +kernel

private theorem check027_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C026_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C027_digit 6 j%5 := by decide +kernel

private theorem check027_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C026_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C027_digit 7 j%5 := by decide +kernel

private theorem check027_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C026_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C027_digit 8 j%5 := by decide +kernel

private theorem check027_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C026_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C027_digit 9 j%5 := by decide +kernel

private theorem check027_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C026_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C027_digit 10 j%5 := by decide +kernel

private theorem check027_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C026_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C027_digit 11 j%5 := by decide +kernel

private theorem check027_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C026_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C027_digit 12 j%5 := by decide +kernel

private theorem check027_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C026_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C027_digit 13 j%5 := by decide +kernel

theorem checks027 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C026_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C027_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check027_00 j
  · exact check027_01 j
  · exact check027_02 j
  · exact check027_03 j
  · exact check027_04 j
  · exact check027_05 j
  · exact check027_06 j
  · exact check027_07 j
  · exact check027_08 j
  · exact check027_09 j
  · exact check027_10 j
  · exact check027_11 j
  · exact check027_12 j
  · exact check027_13 j

theorem matrix_node027 : (node027 A B)=CFSGJankoTwoSelectedCaches04.C027_data.matrix 5 := by
  change (node026 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches03.C026_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches04.C027_data
    CFSGJankoTwoSelectedProducts02.matrix_node026 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks027

private theorem check028_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 0*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 0 j%5 := by decide +kernel

private theorem check028_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 1*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 1 j%5 := by decide +kernel

private theorem check028_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 2*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 2 j%5 := by decide +kernel

private theorem check028_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 3*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 3 j%5 := by decide +kernel

private theorem check028_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 4*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 4 j%5 := by decide +kernel

private theorem check028_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 5*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 5 j%5 := by decide +kernel

private theorem check028_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 6*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 6 j%5 := by decide +kernel

private theorem check028_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 7*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 7 j%5 := by decide +kernel

private theorem check028_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 8*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 8 j%5 := by decide +kernel

private theorem check028_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 9*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 9 j%5 := by decide +kernel

private theorem check028_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 10*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 10 j%5 := by decide +kernel

private theorem check028_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 11*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 11 j%5 := by decide +kernel

private theorem check028_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 12*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 12 j%5 := by decide +kernel

private theorem check028_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 13*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 13 j%5 := by decide +kernel

theorem checks028 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode i*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check028_00 j
  · exact check028_01 j
  · exact check028_02 j
  · exact check028_03 j
  · exact check028_04 j
  · exact check028_05 j
  · exact check028_06 j
  · exact check028_07 j
  · exact check028_08 j
  · exact check028_09 j
  · exact check028_10 j
  · exact check028_11 j
  · exact check028_12 j
  · exact check028_13 j

theorem matrix_node028 : (node028 A B)=CFSGJankoTwoSelectedCaches02.C016_data.matrix 5 := by
  change (node015 A B)*(node015 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches02.C015_data CFSGJankoTwoSelectedCaches02.C015_data CFSGJankoTwoSelectedCaches02.C016_data
    CFSGJankoTwoSelectedProducts01.matrix_node015 CFSGJankoTwoSelectedProducts01.matrix_node015 (by decide : 14*(5-1)^2 < 256) checks028

private theorem check029_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C016_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C029_digit 0 j%5 := by decide +kernel

private theorem check029_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C016_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C029_digit 1 j%5 := by decide +kernel

private theorem check029_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C016_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C029_digit 2 j%5 := by decide +kernel

private theorem check029_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C016_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C029_digit 3 j%5 := by decide +kernel

private theorem check029_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C016_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C029_digit 4 j%5 := by decide +kernel

private theorem check029_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C016_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C029_digit 5 j%5 := by decide +kernel

private theorem check029_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C016_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C029_digit 6 j%5 := by decide +kernel

private theorem check029_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C016_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C029_digit 7 j%5 := by decide +kernel

private theorem check029_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C016_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C029_digit 8 j%5 := by decide +kernel

private theorem check029_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C016_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C029_digit 9 j%5 := by decide +kernel

private theorem check029_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C016_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C029_digit 10 j%5 := by decide +kernel

private theorem check029_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C016_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C029_digit 11 j%5 := by decide +kernel

private theorem check029_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C016_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C029_digit 12 j%5 := by decide +kernel

private theorem check029_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C016_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C029_digit 13 j%5 := by decide +kernel

theorem checks029 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C016_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C029_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check029_00 j
  · exact check029_01 j
  · exact check029_02 j
  · exact check029_03 j
  · exact check029_04 j
  · exact check029_05 j
  · exact check029_06 j
  · exact check029_07 j
  · exact check029_08 j
  · exact check029_09 j
  · exact check029_10 j
  · exact check029_11 j
  · exact check029_12 j
  · exact check029_13 j

theorem matrix_node029 : (node029 A B)=CFSGJankoTwoSelectedCaches04.C029_data.matrix 5 := by
  change (node028 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches02.C016_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches04.C029_data
    CFSGJankoTwoSelectedProducts03.matrix_node028 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks029

private theorem check030_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 0*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 0 j%5 := by decide +kernel

private theorem check030_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 1*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 1 j%5 := by decide +kernel

private theorem check030_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 2*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 2 j%5 := by decide +kernel

private theorem check030_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 3*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 3 j%5 := by decide +kernel

private theorem check030_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 4*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 4 j%5 := by decide +kernel

private theorem check030_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 5*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 5 j%5 := by decide +kernel

private theorem check030_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 6*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 6 j%5 := by decide +kernel

private theorem check030_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 7*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 7 j%5 := by decide +kernel

private theorem check030_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 8*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 8 j%5 := by decide +kernel

private theorem check030_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 9*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 9 j%5 := by decide +kernel

private theorem check030_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 10*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 10 j%5 := by decide +kernel

private theorem check030_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 11*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 11 j%5 := by decide +kernel

private theorem check030_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 12*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 12 j%5 := by decide +kernel

private theorem check030_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 13*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 13 j%5 := by decide +kernel

theorem checks030 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode i*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check030_00 j
  · exact check030_01 j
  · exact check030_02 j
  · exact check030_03 j
  · exact check030_04 j
  · exact check030_05 j
  · exact check030_06 j
  · exact check030_07 j
  · exact check030_08 j
  · exact check030_09 j
  · exact check030_10 j
  · exact check030_11 j
  · exact check030_12 j
  · exact check030_13 j

theorem matrix_node030 : (node030 A B)=CFSGJankoTwoSelectedCaches04.C030_data.matrix 5 := by
  change (node021 A B)*(node021 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches03.C021_data CFSGJankoTwoSelectedCaches03.C021_data CFSGJankoTwoSelectedCaches04.C030_data
    CFSGJankoTwoSelectedProducts02.matrix_node021 CFSGJankoTwoSelectedProducts02.matrix_node021 (by decide : 14*(5-1)^2 < 256) checks030

private theorem check031_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 0*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 0 j%5 := by decide +kernel

private theorem check031_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 1*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 1 j%5 := by decide +kernel

private theorem check031_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 2*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 2 j%5 := by decide +kernel

private theorem check031_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 3*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 3 j%5 := by decide +kernel

private theorem check031_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 4*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 4 j%5 := by decide +kernel

private theorem check031_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 5*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 5 j%5 := by decide +kernel

private theorem check031_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 6*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 6 j%5 := by decide +kernel

private theorem check031_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 7*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 7 j%5 := by decide +kernel

private theorem check031_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 8*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 8 j%5 := by decide +kernel

private theorem check031_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 9*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 9 j%5 := by decide +kernel

private theorem check031_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 10*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 10 j%5 := by decide +kernel

private theorem check031_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 11*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 11 j%5 := by decide +kernel

private theorem check031_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 12*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 12 j%5 := by decide +kernel

private theorem check031_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 13*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 13 j%5 := by decide +kernel

theorem checks031 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode i*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check031_00 j
  · exact check031_01 j
  · exact check031_02 j
  · exact check031_03 j
  · exact check031_04 j
  · exact check031_05 j
  · exact check031_06 j
  · exact check031_07 j
  · exact check031_08 j
  · exact check031_09 j
  · exact check031_10 j
  · exact check031_11 j
  · exact check031_12 j
  · exact check031_13 j

theorem matrix_node031 : (node031 A B)=CFSGJankoTwoSelectedCaches04.C031_data.matrix 5 := by
  change (node027 A B)*(node027 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches04.C027_data CFSGJankoTwoSelectedCaches04.C027_data CFSGJankoTwoSelectedCaches04.C031_data
    CFSGJankoTwoSelectedProducts03.matrix_node027 CFSGJankoTwoSelectedProducts03.matrix_node027 (by decide : 14*(5-1)^2 < 256) checks031

private theorem check032_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 0*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 0 j%5 := by decide +kernel

private theorem check032_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 1*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 1 j%5 := by decide +kernel

private theorem check032_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 2*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 2 j%5 := by decide +kernel

private theorem check032_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 3*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 3 j%5 := by decide +kernel

private theorem check032_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 4*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 4 j%5 := by decide +kernel

private theorem check032_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 5*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 5 j%5 := by decide +kernel

private theorem check032_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 6*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 6 j%5 := by decide +kernel

private theorem check032_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 7*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 7 j%5 := by decide +kernel

private theorem check032_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 8*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 8 j%5 := by decide +kernel

private theorem check032_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 9*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 9 j%5 := by decide +kernel

private theorem check032_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 10*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 10 j%5 := by decide +kernel

private theorem check032_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 11*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 11 j%5 := by decide +kernel

private theorem check032_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 12*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 12 j%5 := by decide +kernel

private theorem check032_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 13*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 13 j%5 := by decide +kernel

theorem checks032 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode i*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check032_00 j
  · exact check032_01 j
  · exact check032_02 j
  · exact check032_03 j
  · exact check032_04 j
  · exact check032_05 j
  · exact check032_06 j
  · exact check032_07 j
  · exact check032_08 j
  · exact check032_09 j
  · exact check032_10 j
  · exact check032_11 j
  · exact check032_12 j
  · exact check032_13 j

theorem matrix_node032 : (node032 A B)=CFSGJankoTwoSelectedCaches04.C032_data.matrix 5 := by
  change (node021 A B)*(node027 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches03.C021_data CFSGJankoTwoSelectedCaches04.C027_data CFSGJankoTwoSelectedCaches04.C032_data
    CFSGJankoTwoSelectedProducts02.matrix_node021 CFSGJankoTwoSelectedProducts03.matrix_node027 (by decide : 14*(5-1)^2 < 256) checks032

private theorem check033_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 0*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C033_digit 0 j%5 := by decide +kernel

private theorem check033_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 1*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C033_digit 1 j%5 := by decide +kernel

private theorem check033_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 2*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C033_digit 2 j%5 := by decide +kernel

private theorem check033_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 3*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C033_digit 3 j%5 := by decide +kernel

private theorem check033_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 4*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C033_digit 4 j%5 := by decide +kernel

private theorem check033_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 5*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C033_digit 5 j%5 := by decide +kernel

private theorem check033_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 6*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C033_digit 6 j%5 := by decide +kernel

private theorem check033_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 7*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C033_digit 7 j%5 := by decide +kernel

private theorem check033_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 8*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C033_digit 8 j%5 := by decide +kernel

private theorem check033_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 9*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C033_digit 9 j%5 := by decide +kernel

private theorem check033_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 10*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C033_digit 10 j%5 := by decide +kernel

private theorem check033_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 11*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C033_digit 11 j%5 := by decide +kernel

private theorem check033_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 12*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C033_digit 12 j%5 := by decide +kernel

private theorem check033_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 13*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C033_digit 13 j%5 := by decide +kernel

theorem checks033 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode i*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C033_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check033_00 j
  · exact check033_01 j
  · exact check033_02 j
  · exact check033_03 j
  · exact check033_04 j
  · exact check033_05 j
  · exact check033_06 j
  · exact check033_07 j
  · exact check033_08 j
  · exact check033_09 j
  · exact check033_10 j
  · exact check033_11 j
  · exact check033_12 j
  · exact check033_13 j

theorem matrix_node033 : (node033 A B)=CFSGJankoTwoSelectedCaches04.C033_data.matrix 5 := by
  change (node032 A B)*(node030 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches04.C032_data CFSGJankoTwoSelectedCaches04.C030_data CFSGJankoTwoSelectedCaches04.C033_data
    CFSGJankoTwoSelectedProducts03.matrix_node032 CFSGJankoTwoSelectedProducts03.matrix_node030 (by decide : 14*(5-1)^2 < 256) checks033

private theorem check034_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C033_rowCode 0*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 0 j%5 := by decide +kernel

private theorem check034_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C033_rowCode 1*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 1 j%5 := by decide +kernel

private theorem check034_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C033_rowCode 2*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 2 j%5 := by decide +kernel

private theorem check034_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C033_rowCode 3*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 3 j%5 := by decide +kernel

private theorem check034_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C033_rowCode 4*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 4 j%5 := by decide +kernel

private theorem check034_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C033_rowCode 5*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 5 j%5 := by decide +kernel

private theorem check034_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C033_rowCode 6*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 6 j%5 := by decide +kernel

private theorem check034_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C033_rowCode 7*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 7 j%5 := by decide +kernel

private theorem check034_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C033_rowCode 8*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 8 j%5 := by decide +kernel

private theorem check034_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C033_rowCode 9*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 9 j%5 := by decide +kernel

private theorem check034_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C033_rowCode 10*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 10 j%5 := by decide +kernel

private theorem check034_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C033_rowCode 11*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 11 j%5 := by decide +kernel

private theorem check034_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C033_rowCode 12*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 12 j%5 := by decide +kernel

private theorem check034_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C033_rowCode 13*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 13 j%5 := by decide +kernel

theorem checks034 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C033_rowCode i*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check034_00 j
  · exact check034_01 j
  · exact check034_02 j
  · exact check034_03 j
  · exact check034_04 j
  · exact check034_05 j
  · exact check034_06 j
  · exact check034_07 j
  · exact check034_08 j
  · exact check034_09 j
  · exact check034_10 j
  · exact check034_11 j
  · exact check034_12 j
  · exact check034_13 j

theorem matrix_node034 : (node034 A B)=CFSGJankoTwoSelectedCaches05.C034_data.matrix 5 := by
  change (node033 A B)*(node031 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches04.C033_data CFSGJankoTwoSelectedCaches04.C031_data CFSGJankoTwoSelectedCaches05.C034_data
    CFSGJankoTwoSelectedProducts03.matrix_node033 CFSGJankoTwoSelectedProducts03.matrix_node031 (by decide : 14*(5-1)^2 < 256) checks034

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts03
