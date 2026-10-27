import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedPositiveWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches04
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches06
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts03
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches05
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts04
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches03
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts02
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches00
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedSeedPowerPilot
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts06
open MatrixKroneckerProductReflection
open CFSGJankoTwoSelectedPositiveWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check051_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C030_rowCode 0*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C051_digit 0 j%5 := by decide +kernel

private theorem check051_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C030_rowCode 1*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C051_digit 1 j%5 := by decide +kernel

private theorem check051_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C030_rowCode 2*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C051_digit 2 j%5 := by decide +kernel

private theorem check051_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C030_rowCode 3*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C051_digit 3 j%5 := by decide +kernel

private theorem check051_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C030_rowCode 4*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C051_digit 4 j%5 := by decide +kernel

private theorem check051_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C030_rowCode 5*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C051_digit 5 j%5 := by decide +kernel

private theorem check051_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C030_rowCode 6*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C051_digit 6 j%5 := by decide +kernel

private theorem check051_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C030_rowCode 7*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C051_digit 7 j%5 := by decide +kernel

private theorem check051_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C030_rowCode 8*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C051_digit 8 j%5 := by decide +kernel

private theorem check051_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C030_rowCode 9*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C051_digit 9 j%5 := by decide +kernel

private theorem check051_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C030_rowCode 10*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C051_digit 10 j%5 := by decide +kernel

private theorem check051_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C030_rowCode 11*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C051_digit 11 j%5 := by decide +kernel

private theorem check051_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C030_rowCode 12*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C051_digit 12 j%5 := by decide +kernel

private theorem check051_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C030_rowCode 13*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C051_digit 13 j%5 := by decide +kernel

theorem checks051 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C030_rowCode i*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C051_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check051_00 j
  · exact check051_01 j
  · exact check051_02 j
  · exact check051_03 j
  · exact check051_04 j
  · exact check051_05 j
  · exact check051_06 j
  · exact check051_07 j
  · exact check051_08 j
  · exact check051_09 j
  · exact check051_10 j
  · exact check051_11 j
  · exact check051_12 j
  · exact check051_13 j

theorem matrix_node051 : (node051 A B)=CFSGJankoTwoSelectedCaches06.C051_data.matrix 5 := by
  change (node030 A B)*(node027 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches04.C030_data CFSGJankoTwoSelectedCaches04.C027_data CFSGJankoTwoSelectedCaches06.C051_data
    CFSGJankoTwoSelectedProducts03.matrix_node030 CFSGJankoTwoSelectedProducts03.matrix_node027 (by decide : 14*(5-1)^2 < 256) checks051

private theorem check052_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C051_rowCode 0*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C052_digit 0 j%5 := by decide +kernel

private theorem check052_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C051_rowCode 1*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C052_digit 1 j%5 := by decide +kernel

private theorem check052_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C051_rowCode 2*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C052_digit 2 j%5 := by decide +kernel

private theorem check052_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C051_rowCode 3*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C052_digit 3 j%5 := by decide +kernel

private theorem check052_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C051_rowCode 4*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C052_digit 4 j%5 := by decide +kernel

private theorem check052_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C051_rowCode 5*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C052_digit 5 j%5 := by decide +kernel

private theorem check052_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C051_rowCode 6*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C052_digit 6 j%5 := by decide +kernel

private theorem check052_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C051_rowCode 7*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C052_digit 7 j%5 := by decide +kernel

private theorem check052_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C051_rowCode 8*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C052_digit 8 j%5 := by decide +kernel

private theorem check052_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C051_rowCode 9*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C052_digit 9 j%5 := by decide +kernel

private theorem check052_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C051_rowCode 10*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C052_digit 10 j%5 := by decide +kernel

private theorem check052_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C051_rowCode 11*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C052_digit 11 j%5 := by decide +kernel

private theorem check052_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C051_rowCode 12*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C052_digit 12 j%5 := by decide +kernel

private theorem check052_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C051_rowCode 13*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C052_digit 13 j%5 := by decide +kernel

theorem checks052 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C051_rowCode i*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C052_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check052_00 j
  · exact check052_01 j
  · exact check052_02 j
  · exact check052_03 j
  · exact check052_04 j
  · exact check052_05 j
  · exact check052_06 j
  · exact check052_07 j
  · exact check052_08 j
  · exact check052_09 j
  · exact check052_10 j
  · exact check052_11 j
  · exact check052_12 j
  · exact check052_13 j

theorem matrix_node052 : (node052 A B)=CFSGJankoTwoSelectedCaches06.C052_data.matrix 5 := by
  change (node051 A B)*(node035 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches06.C051_data CFSGJankoTwoSelectedCaches05.C035_data CFSGJankoTwoSelectedCaches06.C052_data
    CFSGJankoTwoSelectedProducts06.matrix_node051 CFSGJankoTwoSelectedProducts04.matrix_node035 (by decide : 14*(5-1)^2 < 256) checks052

private theorem check053_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C052_rowCode 0*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 0 j%5 := by decide +kernel

private theorem check053_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C052_rowCode 1*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 1 j%5 := by decide +kernel

private theorem check053_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C052_rowCode 2*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 2 j%5 := by decide +kernel

private theorem check053_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C052_rowCode 3*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 3 j%5 := by decide +kernel

private theorem check053_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C052_rowCode 4*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 4 j%5 := by decide +kernel

private theorem check053_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C052_rowCode 5*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 5 j%5 := by decide +kernel

private theorem check053_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C052_rowCode 6*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 6 j%5 := by decide +kernel

private theorem check053_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C052_rowCode 7*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 7 j%5 := by decide +kernel

private theorem check053_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C052_rowCode 8*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 8 j%5 := by decide +kernel

private theorem check053_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C052_rowCode 9*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 9 j%5 := by decide +kernel

private theorem check053_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C052_rowCode 10*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 10 j%5 := by decide +kernel

private theorem check053_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C052_rowCode 11*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 11 j%5 := by decide +kernel

private theorem check053_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C052_rowCode 12*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 12 j%5 := by decide +kernel

private theorem check053_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C052_rowCode 13*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 13 j%5 := by decide +kernel

theorem checks053 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C052_rowCode i*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check053_00 j
  · exact check053_01 j
  · exact check053_02 j
  · exact check053_03 j
  · exact check053_04 j
  · exact check053_05 j
  · exact check053_06 j
  · exact check053_07 j
  · exact check053_08 j
  · exact check053_09 j
  · exact check053_10 j
  · exact check053_11 j
  · exact check053_12 j
  · exact check053_13 j

theorem matrix_node053 : (node053 A B)=CFSGJankoTwoSelectedCaches05.C050_data.matrix 5 := by
  change (node052 A B)*(node029 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches06.C052_data CFSGJankoTwoSelectedCaches04.C029_data CFSGJankoTwoSelectedCaches05.C050_data
    CFSGJankoTwoSelectedProducts06.matrix_node052 CFSGJankoTwoSelectedProducts03.matrix_node029 (by decide : 14*(5-1)^2 < 256) checks053

private theorem check054_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 0*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 0 j%5 := by decide +kernel

private theorem check054_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 1*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 1 j%5 := by decide +kernel

private theorem check054_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 2*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 2 j%5 := by decide +kernel

private theorem check054_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 3*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 3 j%5 := by decide +kernel

private theorem check054_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 4*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 4 j%5 := by decide +kernel

private theorem check054_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 5*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 5 j%5 := by decide +kernel

private theorem check054_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 6*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 6 j%5 := by decide +kernel

private theorem check054_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 7*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 7 j%5 := by decide +kernel

private theorem check054_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 8*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 8 j%5 := by decide +kernel

private theorem check054_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 9*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 9 j%5 := by decide +kernel

private theorem check054_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 10*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 10 j%5 := by decide +kernel

private theorem check054_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 11*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 11 j%5 := by decide +kernel

private theorem check054_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 12*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 12 j%5 := by decide +kernel

private theorem check054_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 13*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 13 j%5 := by decide +kernel

theorem checks054 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode i*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check054_00 j
  · exact check054_01 j
  · exact check054_02 j
  · exact check054_03 j
  · exact check054_04 j
  · exact check054_05 j
  · exact check054_06 j
  · exact check054_07 j
  · exact check054_08 j
  · exact check054_09 j
  · exact check054_10 j
  · exact check054_11 j
  · exact check054_12 j
  · exact check054_13 j

theorem matrix_node054 : (node054 A B)=CFSGJankoTwoSelectedCaches06.C054_data.matrix 5 := by
  change (node029 A B)*(node027 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches04.C029_data CFSGJankoTwoSelectedCaches04.C027_data CFSGJankoTwoSelectedCaches06.C054_data
    CFSGJankoTwoSelectedProducts03.matrix_node029 CFSGJankoTwoSelectedProducts03.matrix_node027 (by decide : 14*(5-1)^2 < 256) checks054

private theorem check055_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 0*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 0 j%5 := by decide +kernel

private theorem check055_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 1*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 1 j%5 := by decide +kernel

private theorem check055_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 2*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 2 j%5 := by decide +kernel

private theorem check055_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 3*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 3 j%5 := by decide +kernel

private theorem check055_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 4*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 4 j%5 := by decide +kernel

private theorem check055_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 5*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 5 j%5 := by decide +kernel

private theorem check055_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 6*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 6 j%5 := by decide +kernel

private theorem check055_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 7*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 7 j%5 := by decide +kernel

private theorem check055_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 8*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 8 j%5 := by decide +kernel

private theorem check055_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 9*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 9 j%5 := by decide +kernel

private theorem check055_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 10*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 10 j%5 := by decide +kernel

private theorem check055_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 11*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 11 j%5 := by decide +kernel

private theorem check055_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 12*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 12 j%5 := by decide +kernel

private theorem check055_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 13*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit 13 j%5 := by decide +kernel

theorem checks055 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode i*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C054_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check055_00 j
  · exact check055_01 j
  · exact check055_02 j
  · exact check055_03 j
  · exact check055_04 j
  · exact check055_05 j
  · exact check055_06 j
  · exact check055_07 j
  · exact check055_08 j
  · exact check055_09 j
  · exact check055_10 j
  · exact check055_11 j
  · exact check055_12 j
  · exact check055_13 j

theorem matrix_node055 : (node055 A B)=CFSGJankoTwoSelectedCaches06.C054_data.matrix 5 := by
  change (node021 A B)*(node029 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches03.C021_data CFSGJankoTwoSelectedCaches04.C029_data CFSGJankoTwoSelectedCaches06.C054_data
    CFSGJankoTwoSelectedProducts02.matrix_node021 CFSGJankoTwoSelectedProducts03.matrix_node029 (by decide : 14*(5-1)^2 < 256) checks055

private theorem check056_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 0*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 0 j%5 := by decide +kernel

private theorem check056_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 1*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 1 j%5 := by decide +kernel

private theorem check056_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 2*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 2 j%5 := by decide +kernel

private theorem check056_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 3*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 3 j%5 := by decide +kernel

private theorem check056_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 4*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 4 j%5 := by decide +kernel

private theorem check056_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 5*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 5 j%5 := by decide +kernel

private theorem check056_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 6*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 6 j%5 := by decide +kernel

private theorem check056_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 7*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 7 j%5 := by decide +kernel

private theorem check056_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 8*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 8 j%5 := by decide +kernel

private theorem check056_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 9*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 9 j%5 := by decide +kernel

private theorem check056_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 10*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 10 j%5 := by decide +kernel

private theorem check056_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 11*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 11 j%5 := by decide +kernel

private theorem check056_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 12*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 12 j%5 := by decide +kernel

private theorem check056_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 13*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 13 j%5 := by decide +kernel

theorem checks056 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode i*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check056_00 j
  · exact check056_01 j
  · exact check056_02 j
  · exact check056_03 j
  · exact check056_04 j
  · exact check056_05 j
  · exact check056_06 j
  · exact check056_07 j
  · exact check056_08 j
  · exact check056_09 j
  · exact check056_10 j
  · exact check056_11 j
  · exact check056_12 j
  · exact check056_13 j

theorem matrix_node056 : (node056 A B)=CFSGJankoTwoSelectedCaches06.C056_data.matrix 5 := by
  change (node029 A B)*(node035 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches04.C029_data CFSGJankoTwoSelectedCaches05.C035_data CFSGJankoTwoSelectedCaches06.C056_data
    CFSGJankoTwoSelectedProducts03.matrix_node029 CFSGJankoTwoSelectedProducts04.matrix_node035 (by decide : 14*(5-1)^2 < 256) checks056

private theorem check057_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 0*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 0 j%5 := by decide +kernel

private theorem check057_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 1*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 1 j%5 := by decide +kernel

private theorem check057_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 2*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 2 j%5 := by decide +kernel

private theorem check057_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 3*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 3 j%5 := by decide +kernel

private theorem check057_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 4*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 4 j%5 := by decide +kernel

private theorem check057_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 5*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 5 j%5 := by decide +kernel

private theorem check057_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 6*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 6 j%5 := by decide +kernel

private theorem check057_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 7*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 7 j%5 := by decide +kernel

private theorem check057_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 8*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 8 j%5 := by decide +kernel

private theorem check057_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 9*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 9 j%5 := by decide +kernel

private theorem check057_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 10*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 10 j%5 := by decide +kernel

private theorem check057_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 11*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 11 j%5 := by decide +kernel

private theorem check057_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 12*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 12 j%5 := by decide +kernel

private theorem check057_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode 13*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit 13 j%5 := by decide +kernel

theorem checks057 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C034_rowCode i*CFSGJankoTwoSelectedCaches04.C029_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C056_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check057_00 j
  · exact check057_01 j
  · exact check057_02 j
  · exact check057_03 j
  · exact check057_04 j
  · exact check057_05 j
  · exact check057_06 j
  · exact check057_07 j
  · exact check057_08 j
  · exact check057_09 j
  · exact check057_10 j
  · exact check057_11 j
  · exact check057_12 j
  · exact check057_13 j

theorem matrix_node057 : (node057 A B)=CFSGJankoTwoSelectedCaches06.C056_data.matrix 5 := by
  change (node036 A B)*(node029 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches05.C034_data CFSGJankoTwoSelectedCaches04.C029_data CFSGJankoTwoSelectedCaches06.C056_data
    CFSGJankoTwoSelectedProducts04.matrix_node036 CFSGJankoTwoSelectedProducts03.matrix_node029 (by decide : 14*(5-1)^2 < 256) checks057

private theorem check062_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 0*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 0 j%5 := by decide +kernel

private theorem check062_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 1*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 1 j%5 := by decide +kernel

private theorem check062_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 2*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 2 j%5 := by decide +kernel

private theorem check062_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 3*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 3 j%5 := by decide +kernel

private theorem check062_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 4*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 4 j%5 := by decide +kernel

private theorem check062_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 5*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 5 j%5 := by decide +kernel

private theorem check062_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 6*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 6 j%5 := by decide +kernel

private theorem check062_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 7*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 7 j%5 := by decide +kernel

private theorem check062_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 8*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 8 j%5 := by decide +kernel

private theorem check062_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 9*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 9 j%5 := by decide +kernel

private theorem check062_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 10*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 10 j%5 := by decide +kernel

private theorem check062_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 11*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 11 j%5 := by decide +kernel

private theorem check062_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 12*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 12 j%5 := by decide +kernel

private theorem check062_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 13*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 13 j%5 := by decide +kernel

theorem checks062 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode i*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check062_00 j
  · exact check062_01 j
  · exact check062_02 j
  · exact check062_03 j
  · exact check062_04 j
  · exact check062_05 j
  · exact check062_06 j
  · exact check062_07 j
  · exact check062_08 j
  · exact check062_09 j
  · exact check062_10 j
  · exact check062_11 j
  · exact check062_12 j
  · exact check062_13 j

theorem matrix_node062 : (node062 A B)=CFSGJankoTwoSelectedCaches00.C003_data.matrix 5 := by
  change (node002 A B)*(node061 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedBaseCaches.I_data CFSGJankoTwoSelectedCaches00.C003_data CFSGJankoTwoSelectedCaches00.C003_data
    (show (1 : Matrix (Fin 14) (Fin 14) (ZMod 5))=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 from CFSGJankoTwoSelectedBaseCaches.identity_binding.symm) CFSGJankoTwoSelectedSeedPowerPilot.matrix_node061 (by decide : 14*(5-1)^2 < 256) checks062

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts06
