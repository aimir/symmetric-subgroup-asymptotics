import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches04
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts02
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches01
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches05
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts00
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches02
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts01
import SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches06
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts03
open MatrixKroneckerProductReflection
open CFSGJankoTwoBinaryRecoveryWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check023_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C022_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C023_digit 0 j%5 := by decide +kernel

private theorem check023_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C022_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C023_digit 1 j%5 := by decide +kernel

private theorem check023_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C022_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C023_digit 2 j%5 := by decide +kernel

private theorem check023_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C022_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C023_digit 3 j%5 := by decide +kernel

private theorem check023_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C022_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C023_digit 4 j%5 := by decide +kernel

private theorem check023_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C022_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C023_digit 5 j%5 := by decide +kernel

private theorem check023_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C022_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C023_digit 6 j%5 := by decide +kernel

private theorem check023_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C022_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C023_digit 7 j%5 := by decide +kernel

private theorem check023_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C022_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C023_digit 8 j%5 := by decide +kernel

private theorem check023_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C022_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C023_digit 9 j%5 := by decide +kernel

private theorem check023_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C022_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C023_digit 10 j%5 := by decide +kernel

private theorem check023_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C022_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C023_digit 11 j%5 := by decide +kernel

private theorem check023_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C022_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C023_digit 12 j%5 := by decide +kernel

private theorem check023_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C022_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C023_digit 13 j%5 := by decide +kernel

theorem checks023 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C022_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches04.C023_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check023_00 j
  · exact check023_01 j
  · exact check023_02 j
  · exact check023_03 j
  · exact check023_04 j
  · exact check023_05 j
  · exact check023_06 j
  · exact check023_07 j
  · exact check023_08 j
  · exact check023_09 j
  · exact check023_10 j
  · exact check023_11 j
  · exact check023_12 j
  · exact check023_13 j

theorem matrix_node023 : (node023 A B)=CFSGJankoTwoBinaryRecoveryCaches04.C023_data.matrix 5 := by
  change (node022 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches04.C022_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoBinaryRecoveryCaches04.C023_data
    CFSGJankoTwoBinaryRecoveryProducts02.matrix_node022 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks023

private theorem check024_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C023_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C024_digit 0 j%5 := by decide +kernel

private theorem check024_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C023_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C024_digit 1 j%5 := by decide +kernel

private theorem check024_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C023_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C024_digit 2 j%5 := by decide +kernel

private theorem check024_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C023_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C024_digit 3 j%5 := by decide +kernel

private theorem check024_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C023_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C024_digit 4 j%5 := by decide +kernel

private theorem check024_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C023_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C024_digit 5 j%5 := by decide +kernel

private theorem check024_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C023_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C024_digit 6 j%5 := by decide +kernel

private theorem check024_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C023_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C024_digit 7 j%5 := by decide +kernel

private theorem check024_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C023_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C024_digit 8 j%5 := by decide +kernel

private theorem check024_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C023_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C024_digit 9 j%5 := by decide +kernel

private theorem check024_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C023_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C024_digit 10 j%5 := by decide +kernel

private theorem check024_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C023_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C024_digit 11 j%5 := by decide +kernel

private theorem check024_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C023_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C024_digit 12 j%5 := by decide +kernel

private theorem check024_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C023_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C024_digit 13 j%5 := by decide +kernel

theorem checks024 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches04.C023_rowCode i*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C024_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check024_00 j
  · exact check024_01 j
  · exact check024_02 j
  · exact check024_03 j
  · exact check024_04 j
  · exact check024_05 j
  · exact check024_06 j
  · exact check024_07 j
  · exact check024_08 j
  · exact check024_09 j
  · exact check024_10 j
  · exact check024_11 j
  · exact check024_12 j
  · exact check024_13 j

theorem matrix_node024 : (node024 A B)=CFSGJankoTwoBinaryRecoveryCaches05.C024_data.matrix 5 := by
  change (node023 A B)*(node008 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches04.C023_data CFSGJankoTwoBinaryRecoveryCaches01.C008_data CFSGJankoTwoBinaryRecoveryCaches05.C024_data
    CFSGJankoTwoBinaryRecoveryProducts03.matrix_node023 CFSGJankoTwoBinaryRecoveryProducts00.matrix_node008 (by decide : 14*(5-1)^2 < 256) checks024

private theorem check025_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C024_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C025_digit 0 j%5 := by decide +kernel

private theorem check025_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C024_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C025_digit 1 j%5 := by decide +kernel

private theorem check025_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C024_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C025_digit 2 j%5 := by decide +kernel

private theorem check025_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C024_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C025_digit 3 j%5 := by decide +kernel

private theorem check025_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C024_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C025_digit 4 j%5 := by decide +kernel

private theorem check025_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C024_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C025_digit 5 j%5 := by decide +kernel

private theorem check025_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C024_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C025_digit 6 j%5 := by decide +kernel

private theorem check025_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C024_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C025_digit 7 j%5 := by decide +kernel

private theorem check025_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C024_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C025_digit 8 j%5 := by decide +kernel

private theorem check025_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C024_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C025_digit 9 j%5 := by decide +kernel

private theorem check025_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C024_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C025_digit 10 j%5 := by decide +kernel

private theorem check025_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C024_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C025_digit 11 j%5 := by decide +kernel

private theorem check025_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C024_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C025_digit 12 j%5 := by decide +kernel

private theorem check025_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C024_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C025_digit 13 j%5 := by decide +kernel

theorem checks025 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C024_rowCode i*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C025_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check025_00 j
  · exact check025_01 j
  · exact check025_02 j
  · exact check025_03 j
  · exact check025_04 j
  · exact check025_05 j
  · exact check025_06 j
  · exact check025_07 j
  · exact check025_08 j
  · exact check025_09 j
  · exact check025_10 j
  · exact check025_11 j
  · exact check025_12 j
  · exact check025_13 j

theorem matrix_node025 : (node025 A B)=CFSGJankoTwoBinaryRecoveryCaches05.C025_data.matrix 5 := by
  change (node024 A B)*(node008 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches05.C024_data CFSGJankoTwoBinaryRecoveryCaches01.C008_data CFSGJankoTwoBinaryRecoveryCaches05.C025_data
    CFSGJankoTwoBinaryRecoveryProducts03.matrix_node024 CFSGJankoTwoBinaryRecoveryProducts00.matrix_node008 (by decide : 14*(5-1)^2 < 256) checks025

private theorem check026_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C025_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C026_digit 0 j%5 := by decide +kernel

private theorem check026_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C025_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C026_digit 1 j%5 := by decide +kernel

private theorem check026_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C025_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C026_digit 2 j%5 := by decide +kernel

private theorem check026_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C025_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C026_digit 3 j%5 := by decide +kernel

private theorem check026_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C025_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C026_digit 4 j%5 := by decide +kernel

private theorem check026_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C025_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C026_digit 5 j%5 := by decide +kernel

private theorem check026_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C025_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C026_digit 6 j%5 := by decide +kernel

private theorem check026_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C025_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C026_digit 7 j%5 := by decide +kernel

private theorem check026_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C025_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C026_digit 8 j%5 := by decide +kernel

private theorem check026_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C025_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C026_digit 9 j%5 := by decide +kernel

private theorem check026_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C025_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C026_digit 10 j%5 := by decide +kernel

private theorem check026_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C025_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C026_digit 11 j%5 := by decide +kernel

private theorem check026_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C025_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C026_digit 12 j%5 := by decide +kernel

private theorem check026_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C025_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C026_digit 13 j%5 := by decide +kernel

theorem checks026 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C025_rowCode i*CFSGJankoTwoBinaryRecoveryCaches01.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C026_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check026_00 j
  · exact check026_01 j
  · exact check026_02 j
  · exact check026_03 j
  · exact check026_04 j
  · exact check026_05 j
  · exact check026_06 j
  · exact check026_07 j
  · exact check026_08 j
  · exact check026_09 j
  · exact check026_10 j
  · exact check026_11 j
  · exact check026_12 j
  · exact check026_13 j

theorem matrix_node026 : (node026 A B)=CFSGJankoTwoBinaryRecoveryCaches05.C026_data.matrix 5 := by
  change (node025 A B)*(node008 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches05.C025_data CFSGJankoTwoBinaryRecoveryCaches01.C008_data CFSGJankoTwoBinaryRecoveryCaches05.C026_data
    CFSGJankoTwoBinaryRecoveryProducts03.matrix_node025 CFSGJankoTwoBinaryRecoveryProducts00.matrix_node008 (by decide : 14*(5-1)^2 < 256) checks026

private theorem check027_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C026_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C027_digit 0 j%5 := by decide +kernel

private theorem check027_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C026_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C027_digit 1 j%5 := by decide +kernel

private theorem check027_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C026_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C027_digit 2 j%5 := by decide +kernel

private theorem check027_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C026_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C027_digit 3 j%5 := by decide +kernel

private theorem check027_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C026_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C027_digit 4 j%5 := by decide +kernel

private theorem check027_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C026_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C027_digit 5 j%5 := by decide +kernel

private theorem check027_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C026_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C027_digit 6 j%5 := by decide +kernel

private theorem check027_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C026_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C027_digit 7 j%5 := by decide +kernel

private theorem check027_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C026_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C027_digit 8 j%5 := by decide +kernel

private theorem check027_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C026_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C027_digit 9 j%5 := by decide +kernel

private theorem check027_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C026_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C027_digit 10 j%5 := by decide +kernel

private theorem check027_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C026_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C027_digit 11 j%5 := by decide +kernel

private theorem check027_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C026_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C027_digit 12 j%5 := by decide +kernel

private theorem check027_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C026_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C027_digit 13 j%5 := by decide +kernel

theorem checks027 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C026_rowCode i*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches05.C027_digit i j%5 := by
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

theorem matrix_node027 : (node027 A B)=CFSGJankoTwoBinaryRecoveryCaches05.C027_data.matrix 5 := by
  change (node026 A B)*(node014 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches05.C026_data CFSGJankoTwoBinaryRecoveryCaches02.C014_data CFSGJankoTwoBinaryRecoveryCaches05.C027_data
    CFSGJankoTwoBinaryRecoveryProducts03.matrix_node026 CFSGJankoTwoBinaryRecoveryProducts01.matrix_node014 (by decide : 14*(5-1)^2 < 256) checks027

private theorem check028_00 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C027_rowCode 0*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C028_digit 0 j%5 := by decide +kernel

private theorem check028_01 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C027_rowCode 1*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C028_digit 1 j%5 := by decide +kernel

private theorem check028_02 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C027_rowCode 2*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C028_digit 2 j%5 := by decide +kernel

private theorem check028_03 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C027_rowCode 3*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C028_digit 3 j%5 := by decide +kernel

private theorem check028_04 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C027_rowCode 4*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C028_digit 4 j%5 := by decide +kernel

private theorem check028_05 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C027_rowCode 5*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C028_digit 5 j%5 := by decide +kernel

private theorem check028_06 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C027_rowCode 6*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C028_digit 6 j%5 := by decide +kernel

private theorem check028_07 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C027_rowCode 7*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C028_digit 7 j%5 := by decide +kernel

private theorem check028_08 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C027_rowCode 8*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C028_digit 8 j%5 := by decide +kernel

private theorem check028_09 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C027_rowCode 9*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C028_digit 9 j%5 := by decide +kernel

private theorem check028_10 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C027_rowCode 10*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C028_digit 10 j%5 := by decide +kernel

private theorem check028_11 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C027_rowCode 11*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C028_digit 11 j%5 := by decide +kernel

private theorem check028_12 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C027_rowCode 12*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C028_digit 12 j%5 := by decide +kernel

private theorem check028_13 : ∀ j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C027_rowCode 13*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C028_digit 13 j%5 := by decide +kernel

theorem checks028 : ∀ i j : Fin 14, (((CFSGJankoTwoBinaryRecoveryCaches05.C027_rowCode i*CFSGJankoTwoBinaryRecoveryCaches02.C014_columnCode j)/256^13)%256)%5=CFSGJankoTwoBinaryRecoveryCaches06.C028_digit i j%5 := by
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

theorem matrix_node028 : (node028 A B)=CFSGJankoTwoBinaryRecoveryCaches06.C028_data.matrix 5 := by
  change (node027 A B)*(node014 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoBinaryRecoveryCaches05.C027_data CFSGJankoTwoBinaryRecoveryCaches02.C014_data CFSGJankoTwoBinaryRecoveryCaches06.C028_data
    CFSGJankoTwoBinaryRecoveryProducts03.matrix_node027 CFSGJankoTwoBinaryRecoveryProducts01.matrix_node014 (by decide : 14*(5-1)^2 < 256) checks028

end SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryProducts03
