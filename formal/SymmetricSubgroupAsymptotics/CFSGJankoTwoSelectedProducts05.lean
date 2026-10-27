import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedPositiveWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches03
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches05
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts02
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts04
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches04
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts03
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts05
open MatrixKroneckerProductReflection
open CFSGJankoTwoSelectedPositiveWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check043_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 0*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 0 j%5 := by decide +kernel

private theorem check043_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 1*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 1 j%5 := by decide +kernel

private theorem check043_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 2*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 2 j%5 := by decide +kernel

private theorem check043_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 3*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 3 j%5 := by decide +kernel

private theorem check043_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 4*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 4 j%5 := by decide +kernel

private theorem check043_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 5*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 5 j%5 := by decide +kernel

private theorem check043_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 6*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 6 j%5 := by decide +kernel

private theorem check043_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 7*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 7 j%5 := by decide +kernel

private theorem check043_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 8*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 8 j%5 := by decide +kernel

private theorem check043_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 9*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 9 j%5 := by decide +kernel

private theorem check043_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 10*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 10 j%5 := by decide +kernel

private theorem check043_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 11*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 11 j%5 := by decide +kernel

private theorem check043_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 12*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 12 j%5 := by decide +kernel

private theorem check043_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 13*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 13 j%5 := by decide +kernel

theorem checks043 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode i*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check043_00 j
  · exact check043_01 j
  · exact check043_02 j
  · exact check043_03 j
  · exact check043_04 j
  · exact check043_05 j
  · exact check043_06 j
  · exact check043_07 j
  · exact check043_08 j
  · exact check043_09 j
  · exact check043_10 j
  · exact check043_11 j
  · exact check043_12 j
  · exact check043_13 j

theorem matrix_node043 : (node043 A B)=CFSGJankoTwoSelectedCaches05.C043_data.matrix 5 := by
  change (node021 A B)*(node035 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches03.C021_data CFSGJankoTwoSelectedCaches05.C035_data CFSGJankoTwoSelectedCaches05.C043_data
    CFSGJankoTwoSelectedProducts02.matrix_node021 CFSGJankoTwoSelectedProducts04.matrix_node035 (by decide : 14*(5-1)^2 < 256) checks043

private theorem check044_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 0*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 0 j%5 := by decide +kernel

private theorem check044_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 1*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 1 j%5 := by decide +kernel

private theorem check044_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 2*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 2 j%5 := by decide +kernel

private theorem check044_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 3*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 3 j%5 := by decide +kernel

private theorem check044_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 4*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 4 j%5 := by decide +kernel

private theorem check044_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 5*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 5 j%5 := by decide +kernel

private theorem check044_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 6*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 6 j%5 := by decide +kernel

private theorem check044_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 7*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 7 j%5 := by decide +kernel

private theorem check044_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 8*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 8 j%5 := by decide +kernel

private theorem check044_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 9*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 9 j%5 := by decide +kernel

private theorem check044_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 10*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 10 j%5 := by decide +kernel

private theorem check044_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 11*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 11 j%5 := by decide +kernel

private theorem check044_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 12*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 12 j%5 := by decide +kernel

private theorem check044_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 13*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit 13 j%5 := by decide +kernel

theorem checks044 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode i*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C043_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check044_00 j
  · exact check044_01 j
  · exact check044_02 j
  · exact check044_03 j
  · exact check044_04 j
  · exact check044_05 j
  · exact check044_06 j
  · exact check044_07 j
  · exact check044_08 j
  · exact check044_09 j
  · exact check044_10 j
  · exact check044_11 j
  · exact check044_12 j
  · exact check044_13 j

theorem matrix_node044 : (node044 A B)=CFSGJankoTwoSelectedCaches05.C043_data.matrix 5 := by
  change (node035 A B)*(node021 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches05.C035_data CFSGJankoTwoSelectedCaches03.C021_data CFSGJankoTwoSelectedCaches05.C043_data
    CFSGJankoTwoSelectedProducts04.matrix_node035 CFSGJankoTwoSelectedProducts02.matrix_node021 (by decide : 14*(5-1)^2 < 256) checks044

private theorem check045_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 0*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 0 j%5 := by decide +kernel

private theorem check045_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 1*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 1 j%5 := by decide +kernel

private theorem check045_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 2*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 2 j%5 := by decide +kernel

private theorem check045_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 3*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 3 j%5 := by decide +kernel

private theorem check045_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 4*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 4 j%5 := by decide +kernel

private theorem check045_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 5*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 5 j%5 := by decide +kernel

private theorem check045_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 6*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 6 j%5 := by decide +kernel

private theorem check045_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 7*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 7 j%5 := by decide +kernel

private theorem check045_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 8*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 8 j%5 := by decide +kernel

private theorem check045_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 9*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 9 j%5 := by decide +kernel

private theorem check045_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 10*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 10 j%5 := by decide +kernel

private theorem check045_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 11*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 11 j%5 := by decide +kernel

private theorem check045_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 12*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 12 j%5 := by decide +kernel

private theorem check045_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 13*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 13 j%5 := by decide +kernel

theorem checks045 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode i*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check045_00 j
  · exact check045_01 j
  · exact check045_02 j
  · exact check045_03 j
  · exact check045_04 j
  · exact check045_05 j
  · exact check045_06 j
  · exact check045_07 j
  · exact check045_08 j
  · exact check045_09 j
  · exact check045_10 j
  · exact check045_11 j
  · exact check045_12 j
  · exact check045_13 j

theorem matrix_node045 : (node045 A B)=CFSGJankoTwoSelectedCaches05.C045_data.matrix 5 := by
  change (node027 A B)*(node035 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches04.C027_data CFSGJankoTwoSelectedCaches05.C035_data CFSGJankoTwoSelectedCaches05.C045_data
    CFSGJankoTwoSelectedProducts03.matrix_node027 CFSGJankoTwoSelectedProducts04.matrix_node035 (by decide : 14*(5-1)^2 < 256) checks045

private theorem check046_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 0*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 0 j%5 := by decide +kernel

private theorem check046_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 1*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 1 j%5 := by decide +kernel

private theorem check046_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 2*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 2 j%5 := by decide +kernel

private theorem check046_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 3*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 3 j%5 := by decide +kernel

private theorem check046_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 4*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 4 j%5 := by decide +kernel

private theorem check046_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 5*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 5 j%5 := by decide +kernel

private theorem check046_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 6*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 6 j%5 := by decide +kernel

private theorem check046_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 7*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 7 j%5 := by decide +kernel

private theorem check046_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 8*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 8 j%5 := by decide +kernel

private theorem check046_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 9*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 9 j%5 := by decide +kernel

private theorem check046_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 10*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 10 j%5 := by decide +kernel

private theorem check046_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 11*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 11 j%5 := by decide +kernel

private theorem check046_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 12*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 12 j%5 := by decide +kernel

private theorem check046_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode 13*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit 13 j%5 := by decide +kernel

theorem checks046 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches05.C035_rowCode i*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C045_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check046_00 j
  · exact check046_01 j
  · exact check046_02 j
  · exact check046_03 j
  · exact check046_04 j
  · exact check046_05 j
  · exact check046_06 j
  · exact check046_07 j
  · exact check046_08 j
  · exact check046_09 j
  · exact check046_10 j
  · exact check046_11 j
  · exact check046_12 j
  · exact check046_13 j

theorem matrix_node046 : (node046 A B)=CFSGJankoTwoSelectedCaches05.C045_data.matrix 5 := by
  change (node035 A B)*(node027 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches05.C035_data CFSGJankoTwoSelectedCaches04.C027_data CFSGJankoTwoSelectedCaches05.C045_data
    CFSGJankoTwoSelectedProducts04.matrix_node035 CFSGJankoTwoSelectedProducts03.matrix_node027 (by decide : 14*(5-1)^2 < 256) checks046

private theorem check047_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 0*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 0 j%5 := by decide +kernel

private theorem check047_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 1*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 1 j%5 := by decide +kernel

private theorem check047_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 2*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 2 j%5 := by decide +kernel

private theorem check047_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 3*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 3 j%5 := by decide +kernel

private theorem check047_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 4*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 4 j%5 := by decide +kernel

private theorem check047_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 5*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 5 j%5 := by decide +kernel

private theorem check047_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 6*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 6 j%5 := by decide +kernel

private theorem check047_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 7*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 7 j%5 := by decide +kernel

private theorem check047_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 8*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 8 j%5 := by decide +kernel

private theorem check047_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 9*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 9 j%5 := by decide +kernel

private theorem check047_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 10*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 10 j%5 := by decide +kernel

private theorem check047_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 11*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 11 j%5 := by decide +kernel

private theorem check047_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 12*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 12 j%5 := by decide +kernel

private theorem check047_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode 13*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 13 j%5 := by decide +kernel

theorem checks047 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C027_rowCode i*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check047_00 j
  · exact check047_01 j
  · exact check047_02 j
  · exact check047_03 j
  · exact check047_04 j
  · exact check047_05 j
  · exact check047_06 j
  · exact check047_07 j
  · exact check047_08 j
  · exact check047_09 j
  · exact check047_10 j
  · exact check047_11 j
  · exact check047_12 j
  · exact check047_13 j

theorem matrix_node047 : (node047 A B)=CFSGJankoTwoSelectedCaches05.C047_data.matrix 5 := by
  change (node027 A B)*(node021 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches04.C027_data CFSGJankoTwoSelectedCaches03.C021_data CFSGJankoTwoSelectedCaches05.C047_data
    CFSGJankoTwoSelectedProducts03.matrix_node027 CFSGJankoTwoSelectedProducts02.matrix_node021 (by decide : 14*(5-1)^2 < 256) checks047

private theorem check048_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 0*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 0 j%5 := by decide +kernel

private theorem check048_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 1*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 1 j%5 := by decide +kernel

private theorem check048_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 2*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 2 j%5 := by decide +kernel

private theorem check048_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 3*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 3 j%5 := by decide +kernel

private theorem check048_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 4*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 4 j%5 := by decide +kernel

private theorem check048_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 5*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 5 j%5 := by decide +kernel

private theorem check048_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 6*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 6 j%5 := by decide +kernel

private theorem check048_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 7*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 7 j%5 := by decide +kernel

private theorem check048_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 8*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 8 j%5 := by decide +kernel

private theorem check048_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 9*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 9 j%5 := by decide +kernel

private theorem check048_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 10*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 10 j%5 := by decide +kernel

private theorem check048_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 11*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 11 j%5 := by decide +kernel

private theorem check048_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 12*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 12 j%5 := by decide +kernel

private theorem check048_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode 13*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit 13 j%5 := by decide +kernel

theorem checks048 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C021_rowCode i*CFSGJankoTwoSelectedCaches04.C027_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches04.C032_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check048_00 j
  · exact check048_01 j
  · exact check048_02 j
  · exact check048_03 j
  · exact check048_04 j
  · exact check048_05 j
  · exact check048_06 j
  · exact check048_07 j
  · exact check048_08 j
  · exact check048_09 j
  · exact check048_10 j
  · exact check048_11 j
  · exact check048_12 j
  · exact check048_13 j

theorem matrix_node048 : (node048 A B)=CFSGJankoTwoSelectedCaches04.C032_data.matrix 5 := by
  change (node021 A B)*(node027 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches03.C021_data CFSGJankoTwoSelectedCaches04.C027_data CFSGJankoTwoSelectedCaches04.C032_data
    CFSGJankoTwoSelectedProducts02.matrix_node021 CFSGJankoTwoSelectedProducts03.matrix_node027 (by decide : 14*(5-1)^2 < 256) checks048

private theorem check049_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 0*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 0 j%5 := by decide +kernel

private theorem check049_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 1*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 1 j%5 := by decide +kernel

private theorem check049_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 2*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 2 j%5 := by decide +kernel

private theorem check049_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 3*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 3 j%5 := by decide +kernel

private theorem check049_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 4*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 4 j%5 := by decide +kernel

private theorem check049_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 5*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 5 j%5 := by decide +kernel

private theorem check049_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 6*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 6 j%5 := by decide +kernel

private theorem check049_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 7*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 7 j%5 := by decide +kernel

private theorem check049_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 8*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 8 j%5 := by decide +kernel

private theorem check049_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 9*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 9 j%5 := by decide +kernel

private theorem check049_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 10*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 10 j%5 := by decide +kernel

private theorem check049_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 11*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 11 j%5 := by decide +kernel

private theorem check049_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 12*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 12 j%5 := by decide +kernel

private theorem check049_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode 13*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit 13 j%5 := by decide +kernel

theorem checks049 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C032_rowCode i*CFSGJankoTwoSelectedCaches05.C035_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C047_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check049_00 j
  · exact check049_01 j
  · exact check049_02 j
  · exact check049_03 j
  · exact check049_04 j
  · exact check049_05 j
  · exact check049_06 j
  · exact check049_07 j
  · exact check049_08 j
  · exact check049_09 j
  · exact check049_10 j
  · exact check049_11 j
  · exact check049_12 j
  · exact check049_13 j

theorem matrix_node049 : (node049 A B)=CFSGJankoTwoSelectedCaches05.C047_data.matrix 5 := by
  change (node048 A B)*(node035 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches04.C032_data CFSGJankoTwoSelectedCaches05.C035_data CFSGJankoTwoSelectedCaches05.C047_data
    CFSGJankoTwoSelectedProducts05.matrix_node048 CFSGJankoTwoSelectedProducts04.matrix_node035 (by decide : 14*(5-1)^2 < 256) checks049

private theorem check050_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 0*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 0 j%5 := by decide +kernel

private theorem check050_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 1*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 1 j%5 := by decide +kernel

private theorem check050_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 2*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 2 j%5 := by decide +kernel

private theorem check050_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 3*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 3 j%5 := by decide +kernel

private theorem check050_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 4*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 4 j%5 := by decide +kernel

private theorem check050_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 5*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 5 j%5 := by decide +kernel

private theorem check050_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 6*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 6 j%5 := by decide +kernel

private theorem check050_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 7*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 7 j%5 := by decide +kernel

private theorem check050_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 8*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 8 j%5 := by decide +kernel

private theorem check050_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 9*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 9 j%5 := by decide +kernel

private theorem check050_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 10*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 10 j%5 := by decide +kernel

private theorem check050_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 11*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 11 j%5 := by decide +kernel

private theorem check050_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 12*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 12 j%5 := by decide +kernel

private theorem check050_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode 13*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit 13 j%5 := by decide +kernel

theorem checks050 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches04.C029_rowCode i*CFSGJankoTwoSelectedCaches03.C021_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches05.C050_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check050_00 j
  · exact check050_01 j
  · exact check050_02 j
  · exact check050_03 j
  · exact check050_04 j
  · exact check050_05 j
  · exact check050_06 j
  · exact check050_07 j
  · exact check050_08 j
  · exact check050_09 j
  · exact check050_10 j
  · exact check050_11 j
  · exact check050_12 j
  · exact check050_13 j

theorem matrix_node050 : (node050 A B)=CFSGJankoTwoSelectedCaches05.C050_data.matrix 5 := by
  change (node029 A B)*(node021 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches04.C029_data CFSGJankoTwoSelectedCaches03.C021_data CFSGJankoTwoSelectedCaches05.C050_data
    CFSGJankoTwoSelectedProducts03.matrix_node029 CFSGJankoTwoSelectedProducts02.matrix_node021 (by decide : 14*(5-1)^2 < 256) checks050

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts05
