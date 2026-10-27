import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches00
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProductPilot
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches01
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts00
open MatrixKroneckerProductReflection
open CFSGJankoTwoBinaryRecoveryWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check005_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C004_rowCode 0*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 0 j%5 := by decide +kernel

private theorem check005_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C004_rowCode 1*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 1 j%5 := by decide +kernel

private theorem check005_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C004_rowCode 2*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 2 j%5 := by decide +kernel

private theorem check005_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C004_rowCode 3*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 3 j%5 := by decide +kernel

private theorem check005_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C004_rowCode 4*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 4 j%5 := by decide +kernel

private theorem check005_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C004_rowCode 5*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 5 j%5 := by decide +kernel

private theorem check005_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C004_rowCode 6*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 6 j%5 := by decide +kernel

private theorem check005_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C004_rowCode 7*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 7 j%5 := by decide +kernel

private theorem check005_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C004_rowCode 8*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 8 j%5 := by decide +kernel

private theorem check005_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C004_rowCode 9*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 9 j%5 := by decide +kernel

private theorem check005_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C004_rowCode 10*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 10 j%5 := by decide +kernel

private theorem check005_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C004_rowCode 11*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 11 j%5 := by decide +kernel

private theorem check005_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C004_rowCode 12*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 12 j%5 := by decide +kernel

private theorem check005_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C004_rowCode 13*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 13 j%5 := by decide +kernel

theorem checks005 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C004_rowCode i*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check005_00 j
  · exact check005_01 j
  · exact check005_02 j
  · exact check005_03 j
  · exact check005_04 j
  · exact check005_05 j
  · exact check005_06 j
  · exact check005_07 j
  · exact check005_08 j
  · exact check005_09 j
  · exact check005_10 j
  · exact check005_11 j
  · exact check005_12 j
  · exact check005_13 j

theorem matrix_node005 : (node005 A B)=CFSGJankoTwoBinaryRecoveryCaches00.C005_data.matrix 5 := by
  change (node004 A B)*(node001 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches00.C004_data CFSGJankoTwoSelectedBaseCaches.B_data CFSGJankoTwoBinaryRecoveryCaches00.C005_data
    CFSGJankoTwoBinaryRecoveryProductPilot.matrix_node004 CFSGJankoTwoSelectedBaseCaches.B_source_binding (by decide : 14*(5-1)^2 < 256) checks005

private theorem check006_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C006_digit 0 j%5 := by decide +kernel

private theorem check006_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C006_digit 1 j%5 := by decide +kernel

private theorem check006_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C006_digit 2 j%5 := by decide +kernel

private theorem check006_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C006_digit 3 j%5 := by decide +kernel

private theorem check006_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C006_digit 4 j%5 := by decide +kernel

private theorem check006_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C006_digit 5 j%5 := by decide +kernel

private theorem check006_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C006_digit 6 j%5 := by decide +kernel

private theorem check006_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C006_digit 7 j%5 := by decide +kernel

private theorem check006_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C006_digit 8 j%5 := by decide +kernel

private theorem check006_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C006_digit 9 j%5 := by decide +kernel

private theorem check006_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C006_digit 10 j%5 := by decide +kernel

private theorem check006_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C006_digit 11 j%5 := by decide +kernel

private theorem check006_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C006_digit 12 j%5 := by decide +kernel

private theorem check006_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C006_digit 13 j%5 := by decide +kernel

theorem checks006 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode i*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C006_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check006_00 j
  · exact check006_01 j
  · exact check006_02 j
  · exact check006_03 j
  · exact check006_04 j
  · exact check006_05 j
  · exact check006_06 j
  · exact check006_07 j
  · exact check006_08 j
  · exact check006_09 j
  · exact check006_10 j
  · exact check006_11 j
  · exact check006_12 j
  · exact check006_13 j

theorem matrix_node006 : (node006 A B)=CFSGJankoTwoBinaryRecoveryCaches00.C006_data.matrix 5 := by
  change (node000 A B)*(node005 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoBinaryRecoveryCaches00.C005_data CFSGJankoTwoBinaryRecoveryCaches00.C006_data
    CFSGJankoTwoSelectedBaseCaches.A_source_binding CFSGJankoTwoBinaryRecoveryProducts00.matrix_node005 (by decide : 14*(5-1)^2 < 256) checks006

private theorem check007_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C006_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C007_digit 0 j%5 := by decide +kernel

private theorem check007_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C006_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C007_digit 1 j%5 := by decide +kernel

private theorem check007_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C006_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C007_digit 2 j%5 := by decide +kernel

private theorem check007_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C006_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C007_digit 3 j%5 := by decide +kernel

private theorem check007_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C006_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C007_digit 4 j%5 := by decide +kernel

private theorem check007_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C006_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C007_digit 5 j%5 := by decide +kernel

private theorem check007_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C006_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C007_digit 6 j%5 := by decide +kernel

private theorem check007_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C006_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C007_digit 7 j%5 := by decide +kernel

private theorem check007_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C006_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C007_digit 8 j%5 := by decide +kernel

private theorem check007_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C006_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C007_digit 9 j%5 := by decide +kernel

private theorem check007_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C006_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C007_digit 10 j%5 := by decide +kernel

private theorem check007_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C006_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C007_digit 11 j%5 := by decide +kernel

private theorem check007_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C006_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C007_digit 12 j%5 := by decide +kernel

private theorem check007_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C006_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C007_digit 13 j%5 := by decide +kernel

theorem checks007 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C006_rowCode i*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C007_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check007_00 j
  · exact check007_01 j
  · exact check007_02 j
  · exact check007_03 j
  · exact check007_04 j
  · exact check007_05 j
  · exact check007_06 j
  · exact check007_07 j
  · exact check007_08 j
  · exact check007_09 j
  · exact check007_10 j
  · exact check007_11 j
  · exact check007_12 j
  · exact check007_13 j

theorem matrix_node007 : (node007 A B)=CFSGJankoTwoBinaryRecoveryCaches01.C007_data.matrix 5 := by
  change (node006 A B)*(node006 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches00.C006_data CFSGJankoTwoBinaryRecoveryCaches00.C006_data CFSGJankoTwoBinaryRecoveryCaches01.C007_data
    CFSGJankoTwoBinaryRecoveryProducts00.matrix_node006 CFSGJankoTwoBinaryRecoveryProducts00.matrix_node006 (by decide : 14*(5-1)^2 < 256) checks007

private theorem check008_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C007_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C008_digit 0 j%5 := by decide +kernel

private theorem check008_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C007_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C008_digit 1 j%5 := by decide +kernel

private theorem check008_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C007_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C008_digit 2 j%5 := by decide +kernel

private theorem check008_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C007_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C008_digit 3 j%5 := by decide +kernel

private theorem check008_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C007_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C008_digit 4 j%5 := by decide +kernel

private theorem check008_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C007_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C008_digit 5 j%5 := by decide +kernel

private theorem check008_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C007_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C008_digit 6 j%5 := by decide +kernel

private theorem check008_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C007_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C008_digit 7 j%5 := by decide +kernel

private theorem check008_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C007_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C008_digit 8 j%5 := by decide +kernel

private theorem check008_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C007_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C008_digit 9 j%5 := by decide +kernel

private theorem check008_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C007_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C008_digit 10 j%5 := by decide +kernel

private theorem check008_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C007_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C008_digit 11 j%5 := by decide +kernel

private theorem check008_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C007_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C008_digit 12 j%5 := by decide +kernel

private theorem check008_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C007_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C008_digit 13 j%5 := by decide +kernel

theorem checks008 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C007_rowCode i*CFSGJankoTwoBinaryRecoveryCaches00.C006_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C008_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check008_00 j
  · exact check008_01 j
  · exact check008_02 j
  · exact check008_03 j
  · exact check008_04 j
  · exact check008_05 j
  · exact check008_06 j
  · exact check008_07 j
  · exact check008_08 j
  · exact check008_09 j
  · exact check008_10 j
  · exact check008_11 j
  · exact check008_12 j
  · exact check008_13 j

theorem matrix_node008 : (node008 A B)=CFSGJankoTwoBinaryRecoveryCaches01.C008_data.matrix 5 := by
  change (node007 A B)*(node006 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches01.C007_data CFSGJankoTwoBinaryRecoveryCaches00.C006_data CFSGJankoTwoBinaryRecoveryCaches01.C008_data
    CFSGJankoTwoBinaryRecoveryProducts00.matrix_node007 CFSGJankoTwoBinaryRecoveryProducts00.matrix_node006 (by decide : 14*(5-1)^2 < 256) checks008

private theorem check009_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C008_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C009_digit 0 j%5 := by decide +kernel

private theorem check009_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C008_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C009_digit 1 j%5 := by decide +kernel

private theorem check009_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C008_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C009_digit 2 j%5 := by decide +kernel

private theorem check009_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C008_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C009_digit 3 j%5 := by decide +kernel

private theorem check009_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C008_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C009_digit 4 j%5 := by decide +kernel

private theorem check009_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C008_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C009_digit 5 j%5 := by decide +kernel

private theorem check009_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C008_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C009_digit 6 j%5 := by decide +kernel

private theorem check009_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C008_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C009_digit 7 j%5 := by decide +kernel

private theorem check009_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C008_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C009_digit 8 j%5 := by decide +kernel

private theorem check009_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C008_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C009_digit 9 j%5 := by decide +kernel

private theorem check009_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C008_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C009_digit 10 j%5 := by decide +kernel

private theorem check009_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C008_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C009_digit 11 j%5 := by decide +kernel

private theorem check009_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C008_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C009_digit 12 j%5 := by decide +kernel

private theorem check009_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C008_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C009_digit 13 j%5 := by decide +kernel

theorem checks009 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C008_rowCode i*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C009_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check009_00 j
  · exact check009_01 j
  · exact check009_02 j
  · exact check009_03 j
  · exact check009_04 j
  · exact check009_05 j
  · exact check009_06 j
  · exact check009_07 j
  · exact check009_08 j
  · exact check009_09 j
  · exact check009_10 j
  · exact check009_11 j
  · exact check009_12 j
  · exact check009_13 j

theorem matrix_node009 : (node009 A B)=CFSGJankoTwoBinaryRecoveryCaches01.C009_data.matrix 5 := by
  change (node008 A B)*(node008 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches01.C008_data CFSGJankoTwoBinaryRecoveryCaches01.C008_data CFSGJankoTwoBinaryRecoveryCaches01.C009_data
    CFSGJankoTwoBinaryRecoveryProducts00.matrix_node008 CFSGJankoTwoBinaryRecoveryProducts00.matrix_node008 (by decide : 14*(5-1)^2 < 256) checks009

private theorem check010_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C009_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C010_digit 0 j%5 := by decide +kernel

private theorem check010_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C009_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C010_digit 1 j%5 := by decide +kernel

private theorem check010_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C009_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C010_digit 2 j%5 := by decide +kernel

private theorem check010_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C009_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C010_digit 3 j%5 := by decide +kernel

private theorem check010_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C009_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C010_digit 4 j%5 := by decide +kernel

private theorem check010_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C009_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C010_digit 5 j%5 := by decide +kernel

private theorem check010_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C009_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C010_digit 6 j%5 := by decide +kernel

private theorem check010_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C009_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C010_digit 7 j%5 := by decide +kernel

private theorem check010_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C009_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C010_digit 8 j%5 := by decide +kernel

private theorem check010_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C009_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C010_digit 9 j%5 := by decide +kernel

private theorem check010_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C009_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C010_digit 10 j%5 := by decide +kernel

private theorem check010_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C009_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C010_digit 11 j%5 := by decide +kernel

private theorem check010_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C009_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C010_digit 12 j%5 := by decide +kernel

private theorem check010_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C009_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C010_digit 13 j%5 := by decide +kernel

theorem checks010 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches01.C009_rowCode i*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches01.C010_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check010_00 j
  · exact check010_01 j
  · exact check010_02 j
  · exact check010_03 j
  · exact check010_04 j
  · exact check010_05 j
  · exact check010_06 j
  · exact check010_07 j
  · exact check010_08 j
  · exact check010_09 j
  · exact check010_10 j
  · exact check010_11 j
  · exact check010_12 j
  · exact check010_13 j

theorem matrix_node010 : (node010 A B)=CFSGJankoTwoBinaryRecoveryCaches01.C010_data.matrix 5 := by
  change (node009 A B)*(node008 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches01.C009_data CFSGJankoTwoBinaryRecoveryCaches01.C008_data CFSGJankoTwoBinaryRecoveryCaches01.C010_data
    CFSGJankoTwoBinaryRecoveryProducts00.matrix_node009 CFSGJankoTwoBinaryRecoveryProducts00.matrix_node008 (by decide : 14*(5-1)^2 < 256) checks010

end SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts00
