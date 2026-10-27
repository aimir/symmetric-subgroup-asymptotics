import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches00
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches01
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches02
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProductPilot
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts00
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches03
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts01
open MatrixKroneckerProductReflection
open CFSGJankoTwoBinaryRecoveryWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check011_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C011_digit 0 j%5 := by decide +kernel

private theorem check011_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C011_digit 1 j%5 := by decide +kernel

private theorem check011_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C011_digit 2 j%5 := by decide +kernel

private theorem check011_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C011_digit 3 j%5 := by decide +kernel

private theorem check011_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C011_digit 4 j%5 := by decide +kernel

private theorem check011_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C011_digit 5 j%5 := by decide +kernel

private theorem check011_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C011_digit 6 j%5 := by decide +kernel

private theorem check011_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C011_digit 7 j%5 := by decide +kernel

private theorem check011_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C011_digit 8 j%5 := by decide +kernel

private theorem check011_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C011_digit 9 j%5 := by decide +kernel

private theorem check011_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C011_digit 10 j%5 := by decide +kernel

private theorem check011_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C011_digit 11 j%5 := by decide +kernel

private theorem check011_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C011_digit 12 j%5 := by decide +kernel

private theorem check011_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C011_digit 13 j%5 := by decide +kernel

theorem checks011 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C003_rowCode i*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C011_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check011_00 j
  · exact check011_01 j
  · exact check011_02 j
  · exact check011_03 j
  · exact check011_04 j
  · exact check011_05 j
  · exact check011_06 j
  · exact check011_07 j
  · exact check011_08 j
  · exact check011_09 j
  · exact check011_10 j
  · exact check011_11 j
  · exact check011_12 j
  · exact check011_13 j

theorem matrix_node011 : (node011 A B)=CFSGJankoTwoBinaryRecoveryCaches02.C011_data.matrix 5 := by
  change (node003 A B)*(node008 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches00.C003_data CFSGJankoTwoBinaryRecoveryCaches01.C008_data CFSGJankoTwoBinaryRecoveryCaches02.C011_data
    CFSGJankoTwoBinaryRecoveryProductPilot.matrix_node003 CFSGJankoTwoBinaryRecoveryProducts00.matrix_node008 (by decide : 14*(5-1)^2 < 256) checks011

private theorem check012_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C011_rowCode 0*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C012_digit 0 j%5 := by decide +kernel

private theorem check012_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C011_rowCode 1*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C012_digit 1 j%5 := by decide +kernel

private theorem check012_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C011_rowCode 2*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C012_digit 2 j%5 := by decide +kernel

private theorem check012_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C011_rowCode 3*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C012_digit 3 j%5 := by decide +kernel

private theorem check012_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C011_rowCode 4*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C012_digit 4 j%5 := by decide +kernel

private theorem check012_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C011_rowCode 5*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C012_digit 5 j%5 := by decide +kernel

private theorem check012_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C011_rowCode 6*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C012_digit 6 j%5 := by decide +kernel

private theorem check012_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C011_rowCode 7*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C012_digit 7 j%5 := by decide +kernel

private theorem check012_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C011_rowCode 8*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C012_digit 8 j%5 := by decide +kernel

private theorem check012_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C011_rowCode 9*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C012_digit 9 j%5 := by decide +kernel

private theorem check012_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C011_rowCode 10*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C012_digit 10 j%5 := by decide +kernel

private theorem check012_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C011_rowCode 11*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C012_digit 11 j%5 := by decide +kernel

private theorem check012_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C011_rowCode 12*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C012_digit 12 j%5 := by decide +kernel

private theorem check012_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C011_rowCode 13*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C012_digit 13 j%5 := by decide +kernel

theorem checks012 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C011_rowCode i*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C012_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check012_00 j
  · exact check012_01 j
  · exact check012_02 j
  · exact check012_03 j
  · exact check012_04 j
  · exact check012_05 j
  · exact check012_06 j
  · exact check012_07 j
  · exact check012_08 j
  · exact check012_09 j
  · exact check012_10 j
  · exact check012_11 j
  · exact check012_12 j
  · exact check012_13 j

theorem matrix_node012 : (node012 A B)=CFSGJankoTwoBinaryRecoveryCaches02.C012_data.matrix 5 := by
  change (node011 A B)*(node001 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches02.C011_data CFSGJankoTwoSelectedBaseCaches.B_data CFSGJankoTwoBinaryRecoveryCaches02.C012_data
    CFSGJankoTwoBinaryRecoveryProducts01.matrix_node011 CFSGJankoTwoSelectedBaseCaches.B_source_binding (by decide : 14*(5-1)^2 < 256) checks012

private theorem check013_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C012_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C013_digit 0 j%5 := by decide +kernel

private theorem check013_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C012_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C013_digit 1 j%5 := by decide +kernel

private theorem check013_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C012_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C013_digit 2 j%5 := by decide +kernel

private theorem check013_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C012_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C013_digit 3 j%5 := by decide +kernel

private theorem check013_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C012_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C013_digit 4 j%5 := by decide +kernel

private theorem check013_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C012_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C013_digit 5 j%5 := by decide +kernel

private theorem check013_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C012_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C013_digit 6 j%5 := by decide +kernel

private theorem check013_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C012_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C013_digit 7 j%5 := by decide +kernel

private theorem check013_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C012_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C013_digit 8 j%5 := by decide +kernel

private theorem check013_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C012_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C013_digit 9 j%5 := by decide +kernel

private theorem check013_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C012_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C013_digit 10 j%5 := by decide +kernel

private theorem check013_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C012_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C013_digit 11 j%5 := by decide +kernel

private theorem check013_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C012_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C013_digit 12 j%5 := by decide +kernel

private theorem check013_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C012_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C013_digit 13 j%5 := by decide +kernel

theorem checks013 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C012_rowCode i*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C013_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check013_00 j
  · exact check013_01 j
  · exact check013_02 j
  · exact check013_03 j
  · exact check013_04 j
  · exact check013_05 j
  · exact check013_06 j
  · exact check013_07 j
  · exact check013_08 j
  · exact check013_09 j
  · exact check013_10 j
  · exact check013_11 j
  · exact check013_12 j
  · exact check013_13 j

theorem matrix_node013 : (node013 A B)=CFSGJankoTwoBinaryRecoveryCaches02.C013_data.matrix 5 := by
  change (node012 A B)*(node012 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches02.C012_data CFSGJankoTwoBinaryRecoveryCaches02.C012_data CFSGJankoTwoBinaryRecoveryCaches02.C013_data
    CFSGJankoTwoBinaryRecoveryProducts01.matrix_node012 CFSGJankoTwoBinaryRecoveryProducts01.matrix_node012 (by decide : 14*(5-1)^2 < 256) checks013

private theorem check014_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C013_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C014_digit 0 j%5 := by decide +kernel

private theorem check014_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C013_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C014_digit 1 j%5 := by decide +kernel

private theorem check014_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C013_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C014_digit 2 j%5 := by decide +kernel

private theorem check014_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C013_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C014_digit 3 j%5 := by decide +kernel

private theorem check014_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C013_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C014_digit 4 j%5 := by decide +kernel

private theorem check014_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C013_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C014_digit 5 j%5 := by decide +kernel

private theorem check014_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C013_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C014_digit 6 j%5 := by decide +kernel

private theorem check014_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C013_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C014_digit 7 j%5 := by decide +kernel

private theorem check014_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C013_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C014_digit 8 j%5 := by decide +kernel

private theorem check014_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C013_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C014_digit 9 j%5 := by decide +kernel

private theorem check014_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C013_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C014_digit 10 j%5 := by decide +kernel

private theorem check014_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C013_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C014_digit 11 j%5 := by decide +kernel

private theorem check014_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C013_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C014_digit 12 j%5 := by decide +kernel

private theorem check014_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C013_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C014_digit 13 j%5 := by decide +kernel

theorem checks014 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches02.C013_rowCode i*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches02.C014_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check014_00 j
  · exact check014_01 j
  · exact check014_02 j
  · exact check014_03 j
  · exact check014_04 j
  · exact check014_05 j
  · exact check014_06 j
  · exact check014_07 j
  · exact check014_08 j
  · exact check014_09 j
  · exact check014_10 j
  · exact check014_11 j
  · exact check014_12 j
  · exact check014_13 j

theorem matrix_node014 : (node014 A B)=CFSGJankoTwoBinaryRecoveryCaches02.C014_data.matrix 5 := by
  change (node013 A B)*(node012 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches02.C013_data CFSGJankoTwoBinaryRecoveryCaches02.C012_data CFSGJankoTwoBinaryRecoveryCaches02.C014_data
    CFSGJankoTwoBinaryRecoveryProducts01.matrix_node013 CFSGJankoTwoBinaryRecoveryProducts01.matrix_node012 (by decide : 14*(5-1)^2 < 256) checks014

private theorem check015_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 0 j%5 := by decide +kernel

private theorem check015_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 1 j%5 := by decide +kernel

private theorem check015_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 2 j%5 := by decide +kernel

private theorem check015_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 3 j%5 := by decide +kernel

private theorem check015_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 4 j%5 := by decide +kernel

private theorem check015_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 5 j%5 := by decide +kernel

private theorem check015_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 6 j%5 := by decide +kernel

private theorem check015_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 7 j%5 := by decide +kernel

private theorem check015_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 8 j%5 := by decide +kernel

private theorem check015_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 9 j%5 := by decide +kernel

private theorem check015_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 10 j%5 := by decide +kernel

private theorem check015_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 11 j%5 := by decide +kernel

private theorem check015_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 12 j%5 := by decide +kernel

private theorem check015_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit 13 j%5 := by decide +kernel

theorem checks015 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode i*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches00.C005_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check015_00 j
  · exact check015_01 j
  · exact check015_02 j
  · exact check015_03 j
  · exact check015_04 j
  · exact check015_05 j
  · exact check015_06 j
  · exact check015_07 j
  · exact check015_08 j
  · exact check015_09 j
  · exact check015_10 j
  · exact check015_11 j
  · exact check015_12 j
  · exact check015_13 j

theorem matrix_node015 : (node015 A B)=CFSGJankoTwoBinaryRecoveryCaches00.C005_data.matrix 5 := by
  change (node002 A B)*(node005 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedBaseCaches.I_data CFSGJankoTwoBinaryRecoveryCaches00.C005_data CFSGJankoTwoBinaryRecoveryCaches00.C005_data
    (show (1 : Matrix (Fin 14) (Fin 14) (ZMod 5))=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 from CFSGJankoTwoSelectedBaseCaches.identity_binding.symm) CFSGJankoTwoBinaryRecoveryProducts00.matrix_node005 (by decide : 14*(5-1)^2 < 256) checks015

private theorem check016_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C005_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C016_digit 0 j%5 := by decide +kernel

private theorem check016_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C005_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C016_digit 1 j%5 := by decide +kernel

private theorem check016_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C005_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C016_digit 2 j%5 := by decide +kernel

private theorem check016_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C005_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C016_digit 3 j%5 := by decide +kernel

private theorem check016_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C005_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C016_digit 4 j%5 := by decide +kernel

private theorem check016_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C005_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C016_digit 5 j%5 := by decide +kernel

private theorem check016_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C005_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C016_digit 6 j%5 := by decide +kernel

private theorem check016_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C005_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C016_digit 7 j%5 := by decide +kernel

private theorem check016_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C005_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C016_digit 8 j%5 := by decide +kernel

private theorem check016_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C005_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C016_digit 9 j%5 := by decide +kernel

private theorem check016_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C005_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C016_digit 10 j%5 := by decide +kernel

private theorem check016_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C005_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C016_digit 11 j%5 := by decide +kernel

private theorem check016_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C005_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C016_digit 12 j%5 := by decide +kernel

private theorem check016_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C005_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C016_digit 13 j%5 := by decide +kernel

theorem checks016 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches00.C005_rowCode i*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C016_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check016_00 j
  · exact check016_01 j
  · exact check016_02 j
  · exact check016_03 j
  · exact check016_04 j
  · exact check016_05 j
  · exact check016_06 j
  · exact check016_07 j
  · exact check016_08 j
  · exact check016_09 j
  · exact check016_10 j
  · exact check016_11 j
  · exact check016_12 j
  · exact check016_13 j

theorem matrix_node016 : (node016 A B)=CFSGJankoTwoBinaryRecoveryCaches03.C016_data.matrix 5 := by
  change (node015 A B)*(node012 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches00.C005_data CFSGJankoTwoBinaryRecoveryCaches02.C012_data CFSGJankoTwoBinaryRecoveryCaches03.C016_data
    CFSGJankoTwoBinaryRecoveryProducts01.matrix_node015 CFSGJankoTwoBinaryRecoveryProducts01.matrix_node012 (by decide : 14*(5-1)^2 < 256) checks016

end SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts01
