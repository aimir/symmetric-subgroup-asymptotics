import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedPositiveWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches05
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts03
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches03
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches04
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts02
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts04
open MatrixKroneckerProductReflection
open CFSGJankoTwoSelectedPositiveWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check035_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 0*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C035_digit 0 j%5 := by decide +kernel

private theorem check035_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 1*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C035_digit 1 j%5 := by decide +kernel

private theorem check035_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 2*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C035_digit 2 j%5 := by decide +kernel

private theorem check035_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 3*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C035_digit 3 j%5 := by decide +kernel

private theorem check035_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 4*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C035_digit 4 j%5 := by decide +kernel

private theorem check035_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 5*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C035_digit 5 j%5 := by decide +kernel

private theorem check035_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 6*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C035_digit 6 j%5 := by decide +kernel

private theorem check035_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 7*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C035_digit 7 j%5 := by decide +kernel

private theorem check035_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 8*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C035_digit 8 j%5 := by decide +kernel

private theorem check035_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 9*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C035_digit 9 j%5 := by decide +kernel

private theorem check035_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 10*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C035_digit 10 j%5 := by decide +kernel

private theorem check035_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 11*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C035_digit 11 j%5 := by decide +kernel

private theorem check035_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 12*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C035_digit 12 j%5 := by decide +kernel

private theorem check035_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 13*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C035_digit 13 j%5 := by decide +kernel

theorem checks035 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode i*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C035_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check035_00 j
  · exact check035_01 j
  · exact check035_02 j
  · exact check035_03 j
  · exact check035_04 j
  · exact check035_05 j
  · exact check035_06 j
  · exact check035_07 j
  · exact check035_08 j
  · exact check035_09 j
  · exact check035_10 j
  · exact check035_11 j
  · exact check035_12 j
  · exact check035_13 j

theorem matrix_node035 : (node035 A B)=CFSGJankoTwoSelectedCaches05.C035_data.matrix 5 := by
  change (node034 A B)*(node034 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches05.C034_data CFSGJankoTwoSelectedCaches05.C034_data CFSGJankoTwoSelectedCaches05.C035_data
    CFSGJankoTwoSelectedProducts03.matrix_node034 CFSGJankoTwoSelectedProducts03.matrix_node034 (by decide : 14*(5-1)^2 < 256) checks035

private theorem check036_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 0*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 0 j%5 := by decide +kernel

private theorem check036_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 1*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 1 j%5 := by decide +kernel

private theorem check036_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 2*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 2 j%5 := by decide +kernel

private theorem check036_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 3*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 3 j%5 := by decide +kernel

private theorem check036_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 4*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 4 j%5 := by decide +kernel

private theorem check036_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 5*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 5 j%5 := by decide +kernel

private theorem check036_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 6*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 6 j%5 := by decide +kernel

private theorem check036_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 7*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 7 j%5 := by decide +kernel

private theorem check036_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 8*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 8 j%5 := by decide +kernel

private theorem check036_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 9*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 9 j%5 := by decide +kernel

private theorem check036_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 10*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 10 j%5 := by decide +kernel

private theorem check036_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 11*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 11 j%5 := by decide +kernel

private theorem check036_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 12*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 12 j%5 := by decide +kernel

private theorem check036_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 13*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 13 j%5 := by decide +kernel

theorem checks036 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode i*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check036_00 j
  · exact check036_01 j
  · exact check036_02 j
  · exact check036_03 j
  · exact check036_04 j
  · exact check036_05 j
  · exact check036_06 j
  · exact check036_07 j
  · exact check036_08 j
  · exact check036_09 j
  · exact check036_10 j
  · exact check036_11 j
  · exact check036_12 j
  · exact check036_13 j

theorem matrix_node036 : (node036 A B)=CFSGJankoTwoSelectedCaches05.C034_data.matrix 5 := by
  change (node035 A B)*(node035 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches05.C035_data CFSGJankoTwoSelectedCaches05.C035_data CFSGJankoTwoSelectedCaches05.C034_data
    CFSGJankoTwoSelectedProducts04.matrix_node035 CFSGJankoTwoSelectedProducts04.matrix_node035 (by decide : 14*(5-1)^2 < 256) checks036

private theorem check037_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 0*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 0 j%5 := by decide +kernel

private theorem check037_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 1*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 1 j%5 := by decide +kernel

private theorem check037_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 2*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 2 j%5 := by decide +kernel

private theorem check037_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 3*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 3 j%5 := by decide +kernel

private theorem check037_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 4*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 4 j%5 := by decide +kernel

private theorem check037_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 5*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 5 j%5 := by decide +kernel

private theorem check037_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 6*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 6 j%5 := by decide +kernel

private theorem check037_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 7*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 7 j%5 := by decide +kernel

private theorem check037_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 8*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 8 j%5 := by decide +kernel

private theorem check037_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 9*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 9 j%5 := by decide +kernel

private theorem check037_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 10*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 10 j%5 := by decide +kernel

private theorem check037_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 11*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 11 j%5 := by decide +kernel

private theorem check037_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 12*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 12 j%5 := by decide +kernel

private theorem check037_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 13*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit 13 j%5 := by decide +kernel

theorem checks037 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode i*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C030_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check037_00 j
  · exact check037_01 j
  · exact check037_02 j
  · exact check037_03 j
  · exact check037_04 j
  · exact check037_05 j
  · exact check037_06 j
  · exact check037_07 j
  · exact check037_08 j
  · exact check037_09 j
  · exact check037_10 j
  · exact check037_11 j
  · exact check037_12 j
  · exact check037_13 j

theorem matrix_node037 : (node037 A B)=CFSGJankoTwoSelectedCaches04.C030_data.matrix 5 := by
  change (node021 A B)*(node021 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches03.C021_data CFSGJankoTwoSelectedCaches03.C021_data CFSGJankoTwoSelectedCaches04.C030_data
    CFSGJankoTwoSelectedProducts02.matrix_node021 CFSGJankoTwoSelectedProducts02.matrix_node021 (by decide : 14*(5-1)^2 < 256) checks037

private theorem check038_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 0*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 0 j%5 := by decide +kernel

private theorem check038_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 1*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 1 j%5 := by decide +kernel

private theorem check038_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 2*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 2 j%5 := by decide +kernel

private theorem check038_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 3*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 3 j%5 := by decide +kernel

private theorem check038_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 4*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 4 j%5 := by decide +kernel

private theorem check038_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 5*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 5 j%5 := by decide +kernel

private theorem check038_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 6*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 6 j%5 := by decide +kernel

private theorem check038_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 7*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 7 j%5 := by decide +kernel

private theorem check038_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 8*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 8 j%5 := by decide +kernel

private theorem check038_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 9*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 9 j%5 := by decide +kernel

private theorem check038_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 10*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 10 j%5 := by decide +kernel

private theorem check038_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 11*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 11 j%5 := by decide +kernel

private theorem check038_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 12*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 12 j%5 := by decide +kernel

private theorem check038_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 13*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 13 j%5 := by decide +kernel

theorem checks038 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode i*CFSGJankoTwoSelectedCaches04.C030_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check038_00 j
  · exact check038_01 j
  · exact check038_02 j
  · exact check038_03 j
  · exact check038_04 j
  · exact check038_05 j
  · exact check038_06 j
  · exact check038_07 j
  · exact check038_08 j
  · exact check038_09 j
  · exact check038_10 j
  · exact check038_11 j
  · exact check038_12 j
  · exact check038_13 j

theorem matrix_node038 : (node038 A B)=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 := by
  change (node021 A B)*(node037 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches03.C021_data CFSGJankoTwoSelectedCaches04.C030_data CFSGJankoTwoSelectedBaseCaches.I_data
    CFSGJankoTwoSelectedProducts02.matrix_node021 CFSGJankoTwoSelectedProducts04.matrix_node037 (by decide : 14*(5-1)^2 < 256) checks038

private theorem check039_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 0*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 0 j%5 := by decide +kernel

private theorem check039_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 1*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 1 j%5 := by decide +kernel

private theorem check039_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 2*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 2 j%5 := by decide +kernel

private theorem check039_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 3*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 3 j%5 := by decide +kernel

private theorem check039_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 4*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 4 j%5 := by decide +kernel

private theorem check039_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 5*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 5 j%5 := by decide +kernel

private theorem check039_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 6*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 6 j%5 := by decide +kernel

private theorem check039_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 7*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 7 j%5 := by decide +kernel

private theorem check039_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 8*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 8 j%5 := by decide +kernel

private theorem check039_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 9*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 9 j%5 := by decide +kernel

private theorem check039_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 10*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 10 j%5 := by decide +kernel

private theorem check039_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 11*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 11 j%5 := by decide +kernel

private theorem check039_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 12*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 12 j%5 := by decide +kernel

private theorem check039_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 13*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit 13 j%5 := by decide +kernel

theorem checks039 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode i*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C031_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check039_00 j
  · exact check039_01 j
  · exact check039_02 j
  · exact check039_03 j
  · exact check039_04 j
  · exact check039_05 j
  · exact check039_06 j
  · exact check039_07 j
  · exact check039_08 j
  · exact check039_09 j
  · exact check039_10 j
  · exact check039_11 j
  · exact check039_12 j
  · exact check039_13 j

theorem matrix_node039 : (node039 A B)=CFSGJankoTwoSelectedCaches04.C031_data.matrix 5 := by
  change (node027 A B)*(node027 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches04.C027_data CFSGJankoTwoSelectedCaches04.C027_data CFSGJankoTwoSelectedCaches04.C031_data
    CFSGJankoTwoSelectedProducts03.matrix_node027 CFSGJankoTwoSelectedProducts03.matrix_node027 (by decide : 14*(5-1)^2 < 256) checks039

private theorem check040_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 0*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 0 j%5 := by decide +kernel

private theorem check040_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 1*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 1 j%5 := by decide +kernel

private theorem check040_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 2*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 2 j%5 := by decide +kernel

private theorem check040_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 3*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 3 j%5 := by decide +kernel

private theorem check040_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 4*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 4 j%5 := by decide +kernel

private theorem check040_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 5*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 5 j%5 := by decide +kernel

private theorem check040_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 6*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 6 j%5 := by decide +kernel

private theorem check040_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 7*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 7 j%5 := by decide +kernel

private theorem check040_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 8*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 8 j%5 := by decide +kernel

private theorem check040_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 9*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 9 j%5 := by decide +kernel

private theorem check040_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 10*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 10 j%5 := by decide +kernel

private theorem check040_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 11*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 11 j%5 := by decide +kernel

private theorem check040_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 12*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 12 j%5 := by decide +kernel

private theorem check040_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 13*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 13 j%5 := by decide +kernel

theorem checks040 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode i*CFSGJankoTwoSelectedCaches04.C031_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check040_00 j
  · exact check040_01 j
  · exact check040_02 j
  · exact check040_03 j
  · exact check040_04 j
  · exact check040_05 j
  · exact check040_06 j
  · exact check040_07 j
  · exact check040_08 j
  · exact check040_09 j
  · exact check040_10 j
  · exact check040_11 j
  · exact check040_12 j
  · exact check040_13 j

theorem matrix_node040 : (node040 A B)=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 := by
  change (node027 A B)*(node039 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches04.C027_data CFSGJankoTwoSelectedCaches04.C031_data CFSGJankoTwoSelectedBaseCaches.I_data
    CFSGJankoTwoSelectedProducts03.matrix_node027 CFSGJankoTwoSelectedProducts04.matrix_node039 (by decide : 14*(5-1)^2 < 256) checks040

private theorem check041_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 0*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 0 j%5 := by decide +kernel

private theorem check041_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 1*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 1 j%5 := by decide +kernel

private theorem check041_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 2*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 2 j%5 := by decide +kernel

private theorem check041_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 3*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 3 j%5 := by decide +kernel

private theorem check041_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 4*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 4 j%5 := by decide +kernel

private theorem check041_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 5*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 5 j%5 := by decide +kernel

private theorem check041_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 6*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 6 j%5 := by decide +kernel

private theorem check041_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 7*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 7 j%5 := by decide +kernel

private theorem check041_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 8*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 8 j%5 := by decide +kernel

private theorem check041_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 9*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 9 j%5 := by decide +kernel

private theorem check041_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 10*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 10 j%5 := by decide +kernel

private theorem check041_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 11*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 11 j%5 := by decide +kernel

private theorem check041_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 12*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 12 j%5 := by decide +kernel

private theorem check041_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 13*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit 13 j%5 := by decide +kernel

theorem checks041 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode i*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C034_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check041_00 j
  · exact check041_01 j
  · exact check041_02 j
  · exact check041_03 j
  · exact check041_04 j
  · exact check041_05 j
  · exact check041_06 j
  · exact check041_07 j
  · exact check041_08 j
  · exact check041_09 j
  · exact check041_10 j
  · exact check041_11 j
  · exact check041_12 j
  · exact check041_13 j

theorem matrix_node041 : (node041 A B)=CFSGJankoTwoSelectedCaches05.C034_data.matrix 5 := by
  change (node035 A B)*(node035 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches05.C035_data CFSGJankoTwoSelectedCaches05.C035_data CFSGJankoTwoSelectedCaches05.C034_data
    CFSGJankoTwoSelectedProducts04.matrix_node035 CFSGJankoTwoSelectedProducts04.matrix_node035 (by decide : 14*(5-1)^2 < 256) checks041

private theorem check042_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 0*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 0 j%5 := by decide +kernel

private theorem check042_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 1*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 1 j%5 := by decide +kernel

private theorem check042_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 2*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 2 j%5 := by decide +kernel

private theorem check042_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 3*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 3 j%5 := by decide +kernel

private theorem check042_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 4*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 4 j%5 := by decide +kernel

private theorem check042_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 5*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 5 j%5 := by decide +kernel

private theorem check042_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 6*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 6 j%5 := by decide +kernel

private theorem check042_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 7*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 7 j%5 := by decide +kernel

private theorem check042_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 8*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 8 j%5 := by decide +kernel

private theorem check042_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 9*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 9 j%5 := by decide +kernel

private theorem check042_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 10*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 10 j%5 := by decide +kernel

private theorem check042_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 11*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 11 j%5 := by decide +kernel

private theorem check042_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 12*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 12 j%5 := by decide +kernel

private theorem check042_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 13*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 13 j%5 := by decide +kernel

theorem checks042 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode i*CFSGJankoTwoSelectedCaches05.C034_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check042_00 j
  · exact check042_01 j
  · exact check042_02 j
  · exact check042_03 j
  · exact check042_04 j
  · exact check042_05 j
  · exact check042_06 j
  · exact check042_07 j
  · exact check042_08 j
  · exact check042_09 j
  · exact check042_10 j
  · exact check042_11 j
  · exact check042_12 j
  · exact check042_13 j

theorem matrix_node042 : (node042 A B)=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 := by
  change (node035 A B)*(node041 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches05.C035_data CFSGJankoTwoSelectedCaches05.C034_data CFSGJankoTwoSelectedBaseCaches.I_data
    CFSGJankoTwoSelectedProducts04.matrix_node035 CFSGJankoTwoSelectedProducts04.matrix_node041 (by decide : 14*(5-1)^2 < 256) checks042

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts04
