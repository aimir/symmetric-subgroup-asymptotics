import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches03
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches02
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts01
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches01
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches04
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts00
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches00
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts02
open MatrixKroneckerProductReflection
open CFSGJankoTwoBinaryRecoveryWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check017_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C016_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C017_digit 0 j%5 := by decide +kernel

private theorem check017_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C016_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C017_digit 1 j%5 := by decide +kernel

private theorem check017_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C016_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C017_digit 2 j%5 := by decide +kernel

private theorem check017_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C016_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C017_digit 3 j%5 := by decide +kernel

private theorem check017_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C016_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C017_digit 4 j%5 := by decide +kernel

private theorem check017_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C016_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C017_digit 5 j%5 := by decide +kernel

private theorem check017_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C016_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C017_digit 6 j%5 := by decide +kernel

private theorem check017_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C016_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C017_digit 7 j%5 := by decide +kernel

private theorem check017_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C016_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C017_digit 8 j%5 := by decide +kernel

private theorem check017_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C016_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C017_digit 9 j%5 := by decide +kernel

private theorem check017_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C016_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C017_digit 10 j%5 := by decide +kernel

private theorem check017_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C016_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C017_digit 11 j%5 := by decide +kernel

private theorem check017_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C016_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C017_digit 12 j%5 := by decide +kernel

private theorem check017_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C016_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C017_digit 13 j%5 := by decide +kernel

theorem checks017 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C016_rowCode i*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C017_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check017_00 j
  · exact check017_01 j
  · exact check017_02 j
  · exact check017_03 j
  · exact check017_04 j
  · exact check017_05 j
  · exact check017_06 j
  · exact check017_07 j
  · exact check017_08 j
  · exact check017_09 j
  · exact check017_10 j
  · exact check017_11 j
  · exact check017_12 j
  · exact check017_13 j

theorem matrix_node017 : (node017 A B)=CFSGJankoTwoBinaryRecoveryCaches03.C017_data.matrix 5 := by
  change (node016 A B)*(node012 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches03.C016_data CFSGJankoTwoBinaryRecoveryCaches02.C012_data CFSGJankoTwoBinaryRecoveryCaches03.C017_data
    CFSGJankoTwoBinaryRecoveryProducts01.matrix_node016 CFSGJankoTwoBinaryRecoveryProducts01.matrix_node012 (by decide : 14*(5-1)^2 < 256) checks017

private theorem check018_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C017_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C018_digit 0 j%5 := by decide +kernel

private theorem check018_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C017_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C018_digit 1 j%5 := by decide +kernel

private theorem check018_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C017_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C018_digit 2 j%5 := by decide +kernel

private theorem check018_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C017_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C018_digit 3 j%5 := by decide +kernel

private theorem check018_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C017_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C018_digit 4 j%5 := by decide +kernel

private theorem check018_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C017_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C018_digit 5 j%5 := by decide +kernel

private theorem check018_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C017_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C018_digit 6 j%5 := by decide +kernel

private theorem check018_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C017_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C018_digit 7 j%5 := by decide +kernel

private theorem check018_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C017_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C018_digit 8 j%5 := by decide +kernel

private theorem check018_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C017_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C018_digit 9 j%5 := by decide +kernel

private theorem check018_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C017_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C018_digit 10 j%5 := by decide +kernel

private theorem check018_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C017_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C018_digit 11 j%5 := by decide +kernel

private theorem check018_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C017_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C018_digit 12 j%5 := by decide +kernel

private theorem check018_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C017_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C018_digit 13 j%5 := by decide +kernel

theorem checks018 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C017_rowCode i*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C018_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check018_00 j
  · exact check018_01 j
  · exact check018_02 j
  · exact check018_03 j
  · exact check018_04 j
  · exact check018_05 j
  · exact check018_06 j
  · exact check018_07 j
  · exact check018_08 j
  · exact check018_09 j
  · exact check018_10 j
  · exact check018_11 j
  · exact check018_12 j
  · exact check018_13 j

theorem matrix_node018 : (node018 A B)=CFSGJankoTwoBinaryRecoveryCaches03.C018_data.matrix 5 := by
  change (node017 A B)*(node012 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches03.C017_data CFSGJankoTwoBinaryRecoveryCaches02.C012_data CFSGJankoTwoBinaryRecoveryCaches03.C018_data
    CFSGJankoTwoBinaryRecoveryProducts02.matrix_node017 CFSGJankoTwoBinaryRecoveryProducts01.matrix_node012 (by decide : 14*(5-1)^2 < 256) checks018

private theorem check019_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C018_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C019_digit 0 j%5 := by decide +kernel

private theorem check019_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C018_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C019_digit 1 j%5 := by decide +kernel

private theorem check019_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C018_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C019_digit 2 j%5 := by decide +kernel

private theorem check019_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C018_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C019_digit 3 j%5 := by decide +kernel

private theorem check019_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C018_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C019_digit 4 j%5 := by decide +kernel

private theorem check019_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C018_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C019_digit 5 j%5 := by decide +kernel

private theorem check019_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C018_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C019_digit 6 j%5 := by decide +kernel

private theorem check019_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C018_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C019_digit 7 j%5 := by decide +kernel

private theorem check019_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C018_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C019_digit 8 j%5 := by decide +kernel

private theorem check019_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C018_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C019_digit 9 j%5 := by decide +kernel

private theorem check019_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C018_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C019_digit 10 j%5 := by decide +kernel

private theorem check019_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C018_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C019_digit 11 j%5 := by decide +kernel

private theorem check019_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C018_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C019_digit 12 j%5 := by decide +kernel

private theorem check019_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C018_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C019_digit 13 j%5 := by decide +kernel

theorem checks019 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C018_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches03.C019_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check019_00 j
  · exact check019_01 j
  · exact check019_02 j
  · exact check019_03 j
  · exact check019_04 j
  · exact check019_05 j
  · exact check019_06 j
  · exact check019_07 j
  · exact check019_08 j
  · exact check019_09 j
  · exact check019_10 j
  · exact check019_11 j
  · exact check019_12 j
  · exact check019_13 j

theorem matrix_node019 : (node019 A B)=CFSGJankoTwoBinaryRecoveryCaches03.C019_data.matrix 5 := by
  change (node018 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches03.C018_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoBinaryRecoveryCaches03.C019_data
    CFSGJankoTwoBinaryRecoveryProducts02.matrix_node018 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks019

private theorem check020_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C019_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C020_digit 0 j%5 := by decide +kernel

private theorem check020_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C019_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C020_digit 1 j%5 := by decide +kernel

private theorem check020_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C019_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C020_digit 2 j%5 := by decide +kernel

private theorem check020_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C019_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C020_digit 3 j%5 := by decide +kernel

private theorem check020_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C019_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C020_digit 4 j%5 := by decide +kernel

private theorem check020_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C019_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C020_digit 5 j%5 := by decide +kernel

private theorem check020_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C019_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C020_digit 6 j%5 := by decide +kernel

private theorem check020_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C019_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C020_digit 7 j%5 := by decide +kernel

private theorem check020_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C019_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C020_digit 8 j%5 := by decide +kernel

private theorem check020_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C019_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C020_digit 9 j%5 := by decide +kernel

private theorem check020_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C019_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C020_digit 10 j%5 := by decide +kernel

private theorem check020_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C019_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C020_digit 11 j%5 := by decide +kernel

private theorem check020_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C019_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C020_digit 12 j%5 := by decide +kernel

private theorem check020_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C019_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C020_digit 13 j%5 := by decide +kernel

theorem checks020 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches03.C019_rowCode i*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C020_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check020_00 j
  · exact check020_01 j
  · exact check020_02 j
  · exact check020_03 j
  · exact check020_04 j
  · exact check020_05 j
  · exact check020_06 j
  · exact check020_07 j
  · exact check020_08 j
  · exact check020_09 j
  · exact check020_10 j
  · exact check020_11 j
  · exact check020_12 j
  · exact check020_13 j

theorem matrix_node020 : (node020 A B)=CFSGJankoTwoBinaryRecoveryCaches04.C020_data.matrix 5 := by
  change (node019 A B)*(node008 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches03.C019_data CFSGJankoTwoBinaryRecoveryCaches01.C008_data CFSGJankoTwoBinaryRecoveryCaches04.C020_data
    CFSGJankoTwoBinaryRecoveryProducts02.matrix_node019 CFSGJankoTwoBinaryRecoveryProducts00.matrix_node008 (by decide : 14*(5-1)^2 < 256) checks020

private theorem check021_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C020_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C021_digit 0 j%5 := by decide +kernel

private theorem check021_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C020_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C021_digit 1 j%5 := by decide +kernel

private theorem check021_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C020_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C021_digit 2 j%5 := by decide +kernel

private theorem check021_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C020_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C021_digit 3 j%5 := by decide +kernel

private theorem check021_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C020_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C021_digit 4 j%5 := by decide +kernel

private theorem check021_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C020_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C021_digit 5 j%5 := by decide +kernel

private theorem check021_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C020_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C021_digit 6 j%5 := by decide +kernel

private theorem check021_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C020_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C021_digit 7 j%5 := by decide +kernel

private theorem check021_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C020_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C021_digit 8 j%5 := by decide +kernel

private theorem check021_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C020_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C021_digit 9 j%5 := by decide +kernel

private theorem check021_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C020_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C021_digit 10 j%5 := by decide +kernel

private theorem check021_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C020_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C021_digit 11 j%5 := by decide +kernel

private theorem check021_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C020_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C021_digit 12 j%5 := by decide +kernel

private theorem check021_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C020_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C021_digit 13 j%5 := by decide +kernel

theorem checks021 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C020_rowCode i*CFSGJankoTwoBinaryRecoveryCaches00.C005_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C021_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check021_00 j
  · exact check021_01 j
  · exact check021_02 j
  · exact check021_03 j
  · exact check021_04 j
  · exact check021_05 j
  · exact check021_06 j
  · exact check021_07 j
  · exact check021_08 j
  · exact check021_09 j
  · exact check021_10 j
  · exact check021_11 j
  · exact check021_12 j
  · exact check021_13 j

theorem matrix_node021 : (node021 A B)=CFSGJankoTwoBinaryRecoveryCaches04.C021_data.matrix 5 := by
  change (node020 A B)*(node005 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches04.C020_data CFSGJankoTwoBinaryRecoveryCaches00.C005_data CFSGJankoTwoBinaryRecoveryCaches04.C021_data
    CFSGJankoTwoBinaryRecoveryProducts02.matrix_node020 CFSGJankoTwoBinaryRecoveryProducts00.matrix_node005 (by decide : 14*(5-1)^2 < 256) checks021

private theorem check022_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C021_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C022_digit 0 j%5 := by decide +kernel

private theorem check022_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C021_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C022_digit 1 j%5 := by decide +kernel

private theorem check022_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C021_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C022_digit 2 j%5 := by decide +kernel

private theorem check022_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C021_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C022_digit 3 j%5 := by decide +kernel

private theorem check022_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C021_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C022_digit 4 j%5 := by decide +kernel

private theorem check022_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C021_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C022_digit 5 j%5 := by decide +kernel

private theorem check022_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C021_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C022_digit 6 j%5 := by decide +kernel

private theorem check022_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C021_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C022_digit 7 j%5 := by decide +kernel

private theorem check022_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C021_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C022_digit 8 j%5 := by decide +kernel

private theorem check022_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C021_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C022_digit 9 j%5 := by decide +kernel

private theorem check022_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C021_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C022_digit 10 j%5 := by decide +kernel

private theorem check022_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C021_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C022_digit 11 j%5 := by decide +kernel

private theorem check022_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C021_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C022_digit 12 j%5 := by decide +kernel

private theorem check022_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C021_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C022_digit 13 j%5 := by decide +kernel

theorem checks022 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C021_rowCode i*CFSGJankoTwoBinaryRecoveryCaches02.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C022_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check022_00 j
  · exact check022_01 j
  · exact check022_02 j
  · exact check022_03 j
  · exact check022_04 j
  · exact check022_05 j
  · exact check022_06 j
  · exact check022_07 j
  · exact check022_08 j
  · exact check022_09 j
  · exact check022_10 j
  · exact check022_11 j
  · exact check022_12 j
  · exact check022_13 j

theorem matrix_node022 : (node022 A B)=CFSGJankoTwoBinaryRecoveryCaches04.C022_data.matrix 5 := by
  change (node021 A B)*(node012 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches04.C021_data CFSGJankoTwoBinaryRecoveryCaches02.C012_data CFSGJankoTwoBinaryRecoveryCaches04.C022_data
    CFSGJankoTwoBinaryRecoveryProducts02.matrix_node021 CFSGJankoTwoBinaryRecoveryProducts01.matrix_node012 (by decide : 14*(5-1)^2 < 256) checks022

end SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts02
