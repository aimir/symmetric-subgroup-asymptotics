import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches00
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProductPilot
open MatrixKroneckerProductReflection
open CFSGJankoTwoBinaryRecoveryWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check003_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 0*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C003_digit 0 j%5 := by decide +kernel

private theorem check003_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 1*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C003_digit 1 j%5 := by decide +kernel

private theorem check003_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 2*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C003_digit 2 j%5 := by decide +kernel

private theorem check003_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 3*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C003_digit 3 j%5 := by decide +kernel

private theorem check003_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 4*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C003_digit 4 j%5 := by decide +kernel

private theorem check003_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 5*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C003_digit 5 j%5 := by decide +kernel

private theorem check003_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 6*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C003_digit 6 j%5 := by decide +kernel

private theorem check003_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 7*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C003_digit 7 j%5 := by decide +kernel

private theorem check003_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 8*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C003_digit 8 j%5 := by decide +kernel

private theorem check003_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 9*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C003_digit 9 j%5 := by decide +kernel

private theorem check003_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 10*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C003_digit 10 j%5 := by decide +kernel

private theorem check003_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 11*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C003_digit 11 j%5 := by decide +kernel

private theorem check003_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 12*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C003_digit 12 j%5 := by decide +kernel

private theorem check003_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 13*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C003_digit 13 j%5 := by decide +kernel

theorem checks003 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode i*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C003_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check003_00 j
  · exact check003_01 j
  · exact check003_02 j
  · exact check003_03 j
  · exact check003_04 j
  · exact check003_05 j
  · exact check003_06 j
  · exact check003_07 j
  · exact check003_08 j
  · exact check003_09 j
  · exact check003_10 j
  · exact check003_11 j
  · exact check003_12 j
  · exact check003_13 j

theorem matrix_node003 : (node003 A B)=CFSGJankoTwoBinaryRecoveryCaches00.C003_data.matrix 5 := by
  change (node001 A B)*(node001 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedBaseCaches.B_data CFSGJankoTwoSelectedBaseCaches.B_data CFSGJankoTwoBinaryRecoveryCaches00.C003_data
    CFSGJankoTwoSelectedBaseCaches.B_source_binding CFSGJankoTwoSelectedBaseCaches.B_source_binding (by decide : 14*(5-1)^2 < 256) checks003

private theorem check004_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C004_digit 0 j%5 := by decide +kernel

private theorem check004_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C004_digit 1 j%5 := by decide +kernel

private theorem check004_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C004_digit 2 j%5 := by decide +kernel

private theorem check004_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C004_digit 3 j%5 := by decide +kernel

private theorem check004_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C004_digit 4 j%5 := by decide +kernel

private theorem check004_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C004_digit 5 j%5 := by decide +kernel

private theorem check004_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C004_digit 6 j%5 := by decide +kernel

private theorem check004_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C004_digit 7 j%5 := by decide +kernel

private theorem check004_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C004_digit 8 j%5 := by decide +kernel

private theorem check004_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C004_digit 9 j%5 := by decide +kernel

private theorem check004_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C004_digit 10 j%5 := by decide +kernel

private theorem check004_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C004_digit 11 j%5 := by decide +kernel

private theorem check004_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C004_digit 12 j%5 := by decide +kernel

private theorem check004_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C004_digit 13 j%5 := by decide +kernel

theorem checks004 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C004_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check004_00 j
  · exact check004_01 j
  · exact check004_02 j
  · exact check004_03 j
  · exact check004_04 j
  · exact check004_05 j
  · exact check004_06 j
  · exact check004_07 j
  · exact check004_08 j
  · exact check004_09 j
  · exact check004_10 j
  · exact check004_11 j
  · exact check004_12 j
  · exact check004_13 j

theorem matrix_node004 : (node004 A B)=CFSGJankoTwoBinaryRecoveryCaches00.C004_data.matrix 5 := by
  change (node003 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches00.C003_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoBinaryRecoveryCaches00.C004_data
    CFSGJankoTwoBinaryRecoveryProductPilot.matrix_node003 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks004

end SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProductPilot
