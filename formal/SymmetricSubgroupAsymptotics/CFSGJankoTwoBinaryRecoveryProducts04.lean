import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches06
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches02
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts03
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts01
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches01
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts00
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches07
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches00
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts04
open MatrixKroneckerProductReflection
open CFSGJankoTwoBinaryRecoveryWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check029_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C028_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C029_digit 0 j%5 := by decide +kernel

private theorem check029_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C028_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C029_digit 1 j%5 := by decide +kernel

private theorem check029_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C028_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C029_digit 2 j%5 := by decide +kernel

private theorem check029_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C028_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C029_digit 3 j%5 := by decide +kernel

private theorem check029_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C028_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C029_digit 4 j%5 := by decide +kernel

private theorem check029_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C028_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C029_digit 5 j%5 := by decide +kernel

private theorem check029_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C028_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C029_digit 6 j%5 := by decide +kernel

private theorem check029_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C028_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C029_digit 7 j%5 := by decide +kernel

private theorem check029_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C028_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C029_digit 8 j%5 := by decide +kernel

private theorem check029_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C028_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C029_digit 9 j%5 := by decide +kernel

private theorem check029_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C028_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C029_digit 10 j%5 := by decide +kernel

private theorem check029_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C028_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C029_digit 11 j%5 := by decide +kernel

private theorem check029_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C028_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C029_digit 12 j%5 := by decide +kernel

private theorem check029_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C028_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C029_digit 13 j%5 := by decide +kernel

theorem checks029 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C028_rowCode i*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C029_digit i j%5 := by
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

theorem matrix_node029 : (node029 A B)=CFSGJankoTwoBinaryRecoveryCaches06.C029_data.matrix 5 := by
  change (node028 A B)*(node014 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches06.C028_data CFSGJankoTwoBinaryRecoveryCaches02.C014_data CFSGJankoTwoBinaryRecoveryCaches06.C029_data
    CFSGJankoTwoBinaryRecoveryProducts03.matrix_node028 CFSGJankoTwoBinaryRecoveryProducts01.matrix_node014 (by decide : 14*(5-1)^2 < 256) checks029

private theorem check030_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C029_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C030_digit 0 j%5 := by decide +kernel

private theorem check030_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C029_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C030_digit 1 j%5 := by decide +kernel

private theorem check030_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C029_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C030_digit 2 j%5 := by decide +kernel

private theorem check030_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C029_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C030_digit 3 j%5 := by decide +kernel

private theorem check030_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C029_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C030_digit 4 j%5 := by decide +kernel

private theorem check030_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C029_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C030_digit 5 j%5 := by decide +kernel

private theorem check030_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C029_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C030_digit 6 j%5 := by decide +kernel

private theorem check030_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C029_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C030_digit 7 j%5 := by decide +kernel

private theorem check030_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C029_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C030_digit 8 j%5 := by decide +kernel

private theorem check030_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C029_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C030_digit 9 j%5 := by decide +kernel

private theorem check030_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C029_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C030_digit 10 j%5 := by decide +kernel

private theorem check030_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C029_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C030_digit 11 j%5 := by decide +kernel

private theorem check030_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C029_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C030_digit 12 j%5 := by decide +kernel

private theorem check030_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C029_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C030_digit 13 j%5 := by decide +kernel

theorem checks030 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C029_rowCode i*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C030_digit i j%5 := by
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

theorem matrix_node030 : (node030 A B)=CFSGJankoTwoBinaryRecoveryCaches06.C030_data.matrix 5 := by
  change (node029 A B)*(node010 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches06.C029_data CFSGJankoTwoBinaryRecoveryCaches01.C010_data CFSGJankoTwoBinaryRecoveryCaches06.C030_data
    CFSGJankoTwoBinaryRecoveryProducts04.matrix_node029 CFSGJankoTwoBinaryRecoveryProducts00.matrix_node010 (by decide : 14*(5-1)^2 < 256) checks030

private theorem check031_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C030_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C031_digit 0 j%5 := by decide +kernel

private theorem check031_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C030_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C031_digit 1 j%5 := by decide +kernel

private theorem check031_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C030_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C031_digit 2 j%5 := by decide +kernel

private theorem check031_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C030_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C031_digit 3 j%5 := by decide +kernel

private theorem check031_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C030_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C031_digit 4 j%5 := by decide +kernel

private theorem check031_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C030_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C031_digit 5 j%5 := by decide +kernel

private theorem check031_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C030_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C031_digit 6 j%5 := by decide +kernel

private theorem check031_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C030_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C031_digit 7 j%5 := by decide +kernel

private theorem check031_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C030_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C031_digit 8 j%5 := by decide +kernel

private theorem check031_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C030_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C031_digit 9 j%5 := by decide +kernel

private theorem check031_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C030_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C031_digit 10 j%5 := by decide +kernel

private theorem check031_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C030_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C031_digit 11 j%5 := by decide +kernel

private theorem check031_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C030_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C031_digit 12 j%5 := by decide +kernel

private theorem check031_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C030_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C031_digit 13 j%5 := by decide +kernel

theorem checks031 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C030_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C031_digit i j%5 := by
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

theorem matrix_node031 : (node031 A B)=CFSGJankoTwoBinaryRecoveryCaches06.C031_data.matrix 5 := by
  change (node030 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches06.C030_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoBinaryRecoveryCaches06.C031_data
    CFSGJankoTwoBinaryRecoveryProducts04.matrix_node030 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks031

private theorem check032_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C031_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C032_digit 0 j%5 := by decide +kernel

private theorem check032_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C031_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C032_digit 1 j%5 := by decide +kernel

private theorem check032_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C031_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C032_digit 2 j%5 := by decide +kernel

private theorem check032_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C031_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C032_digit 3 j%5 := by decide +kernel

private theorem check032_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C031_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C032_digit 4 j%5 := by decide +kernel

private theorem check032_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C031_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C032_digit 5 j%5 := by decide +kernel

private theorem check032_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C031_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C032_digit 6 j%5 := by decide +kernel

private theorem check032_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C031_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C032_digit 7 j%5 := by decide +kernel

private theorem check032_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C031_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C032_digit 8 j%5 := by decide +kernel

private theorem check032_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C031_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C032_digit 9 j%5 := by decide +kernel

private theorem check032_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C031_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C032_digit 10 j%5 := by decide +kernel

private theorem check032_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C031_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C032_digit 11 j%5 := by decide +kernel

private theorem check032_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C031_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C032_digit 12 j%5 := by decide +kernel

private theorem check032_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C031_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C032_digit 13 j%5 := by decide +kernel

theorem checks032 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches06.C031_rowCode i*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C032_digit i j%5 := by
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

theorem matrix_node032 : (node032 A B)=CFSGJankoTwoBinaryRecoveryCaches07.C032_data.matrix 5 := by
  change (node031 A B)*(node014 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches06.C031_data CFSGJankoTwoBinaryRecoveryCaches02.C014_data CFSGJankoTwoBinaryRecoveryCaches07.C032_data
    CFSGJankoTwoBinaryRecoveryProducts04.matrix_node031 CFSGJankoTwoBinaryRecoveryProducts01.matrix_node014 (by decide : 14*(5-1)^2 < 256) checks032

private theorem check033_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C032_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C033_digit 0 j%5 := by decide +kernel

private theorem check033_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C032_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C033_digit 1 j%5 := by decide +kernel

private theorem check033_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C032_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C033_digit 2 j%5 := by decide +kernel

private theorem check033_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C032_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C033_digit 3 j%5 := by decide +kernel

private theorem check033_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C032_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C033_digit 4 j%5 := by decide +kernel

private theorem check033_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C032_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C033_digit 5 j%5 := by decide +kernel

private theorem check033_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C032_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C033_digit 6 j%5 := by decide +kernel

private theorem check033_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C032_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C033_digit 7 j%5 := by decide +kernel

private theorem check033_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C032_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C033_digit 8 j%5 := by decide +kernel

private theorem check033_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C032_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C033_digit 9 j%5 := by decide +kernel

private theorem check033_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C032_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C033_digit 10 j%5 := by decide +kernel

private theorem check033_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C032_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C033_digit 11 j%5 := by decide +kernel

private theorem check033_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C032_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C033_digit 12 j%5 := by decide +kernel

private theorem check033_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C032_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C033_digit 13 j%5 := by decide +kernel

theorem checks033 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C032_rowCode i*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches07.C033_digit i j%5 := by
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

theorem matrix_node033 : (node033 A B)=CFSGJankoTwoBinaryRecoveryCaches07.C033_data.matrix 5 := by
  change (node032 A B)*(node005 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches07.C032_data CFSGJankoTwoBinaryRecoveryCaches00.C005_data CFSGJankoTwoBinaryRecoveryCaches07.C033_data
    CFSGJankoTwoBinaryRecoveryProducts04.matrix_node032 CFSGJankoTwoBinaryRecoveryProducts00.matrix_node005 (by decide : 14*(5-1)^2 < 256) checks033

private theorem check034_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C033_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.B_digit 0 j%5 := by decide +kernel

private theorem check034_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C033_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.B_digit 1 j%5 := by decide +kernel

private theorem check034_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C033_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.B_digit 2 j%5 := by decide +kernel

private theorem check034_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C033_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.B_digit 3 j%5 := by decide +kernel

private theorem check034_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C033_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.B_digit 4 j%5 := by decide +kernel

private theorem check034_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C033_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.B_digit 5 j%5 := by decide +kernel

private theorem check034_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C033_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.B_digit 6 j%5 := by decide +kernel

private theorem check034_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C033_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.B_digit 7 j%5 := by decide +kernel

private theorem check034_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C033_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.B_digit 8 j%5 := by decide +kernel

private theorem check034_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C033_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.B_digit 9 j%5 := by decide +kernel

private theorem check034_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C033_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.B_digit 10 j%5 := by decide +kernel

private theorem check034_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C033_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.B_digit 11 j%5 := by decide +kernel

private theorem check034_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C033_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.B_digit 12 j%5 := by decide +kernel

private theorem check034_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C033_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.B_digit 13 j%5 := by decide +kernel

theorem checks034 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches07.C033_rowCode i*CFSGJankoTwoBinaryRecoveryCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.B_digit i j%5 := by
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

theorem matrix_node034 : (node034 A B)=CFSGJankoTwoSelectedBaseCaches.B_data.matrix 5 := by
  change (node033 A B)*(node010 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches07.C033_data CFSGJankoTwoBinaryRecoveryCaches01.C010_data CFSGJankoTwoSelectedBaseCaches.B_data
    CFSGJankoTwoBinaryRecoveryProducts04.matrix_node033 CFSGJankoTwoBinaryRecoveryProducts00.matrix_node010 (by decide : 14*(5-1)^2 < 256) checks034

end SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts04
