import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedPositiveWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches02
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts01
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches03
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts02
open MatrixKroneckerProductReflection
open CFSGJankoTwoSelectedPositiveWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check019_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C018_rowCode 0*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C019_digit 0 j%5 := by decide +kernel

private theorem check019_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C018_rowCode 1*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C019_digit 1 j%5 := by decide +kernel

private theorem check019_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C018_rowCode 2*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C019_digit 2 j%5 := by decide +kernel

private theorem check019_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C018_rowCode 3*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C019_digit 3 j%5 := by decide +kernel

private theorem check019_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C018_rowCode 4*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C019_digit 4 j%5 := by decide +kernel

private theorem check019_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C018_rowCode 5*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C019_digit 5 j%5 := by decide +kernel

private theorem check019_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C018_rowCode 6*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C019_digit 6 j%5 := by decide +kernel

private theorem check019_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C018_rowCode 7*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C019_digit 7 j%5 := by decide +kernel

private theorem check019_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C018_rowCode 8*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C019_digit 8 j%5 := by decide +kernel

private theorem check019_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C018_rowCode 9*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C019_digit 9 j%5 := by decide +kernel

private theorem check019_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C018_rowCode 10*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C019_digit 10 j%5 := by decide +kernel

private theorem check019_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C018_rowCode 11*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C019_digit 11 j%5 := by decide +kernel

private theorem check019_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C018_rowCode 12*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C019_digit 12 j%5 := by decide +kernel

private theorem check019_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C018_rowCode 13*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C019_digit 13 j%5 := by decide +kernel

theorem checks019 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C018_rowCode i*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C019_digit i j%5 := by
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

theorem matrix_node019 : (node019 A B)=CFSGJankoTwoSelectedCaches02.C019_data.matrix 5 := by
  change (node018 A B)*(node015 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches02.C018_data CFSGJankoTwoSelectedCaches02.C015_data CFSGJankoTwoSelectedCaches02.C019_data
    CFSGJankoTwoSelectedProducts01.matrix_node018 CFSGJankoTwoSelectedProducts01.matrix_node015 (by decide : 14*(5-1)^2 < 256) checks019

private theorem check020_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C019_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C020_digit 0 j%5 := by decide +kernel

private theorem check020_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C019_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C020_digit 1 j%5 := by decide +kernel

private theorem check020_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C019_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C020_digit 2 j%5 := by decide +kernel

private theorem check020_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C019_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C020_digit 3 j%5 := by decide +kernel

private theorem check020_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C019_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C020_digit 4 j%5 := by decide +kernel

private theorem check020_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C019_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C020_digit 5 j%5 := by decide +kernel

private theorem check020_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C019_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C020_digit 6 j%5 := by decide +kernel

private theorem check020_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C019_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C020_digit 7 j%5 := by decide +kernel

private theorem check020_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C019_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C020_digit 8 j%5 := by decide +kernel

private theorem check020_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C019_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C020_digit 9 j%5 := by decide +kernel

private theorem check020_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C019_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C020_digit 10 j%5 := by decide +kernel

private theorem check020_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C019_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C020_digit 11 j%5 := by decide +kernel

private theorem check020_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C019_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C020_digit 12 j%5 := by decide +kernel

private theorem check020_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C019_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C020_digit 13 j%5 := by decide +kernel

theorem checks020 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C019_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C020_digit i j%5 := by
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

theorem matrix_node020 : (node020 A B)=CFSGJankoTwoSelectedCaches02.C020_data.matrix 5 := by
  change (node019 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches02.C019_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches02.C020_data
    CFSGJankoTwoSelectedProducts02.matrix_node019 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks020

private theorem check021_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C020_rowCode 0*CFSGJankoTwoSelectedCaches02.C017_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C021_digit 0 j%5 := by decide +kernel

private theorem check021_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C020_rowCode 1*CFSGJankoTwoSelectedCaches02.C017_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C021_digit 1 j%5 := by decide +kernel

private theorem check021_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C020_rowCode 2*CFSGJankoTwoSelectedCaches02.C017_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C021_digit 2 j%5 := by decide +kernel

private theorem check021_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C020_rowCode 3*CFSGJankoTwoSelectedCaches02.C017_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C021_digit 3 j%5 := by decide +kernel

private theorem check021_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C020_rowCode 4*CFSGJankoTwoSelectedCaches02.C017_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C021_digit 4 j%5 := by decide +kernel

private theorem check021_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C020_rowCode 5*CFSGJankoTwoSelectedCaches02.C017_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C021_digit 5 j%5 := by decide +kernel

private theorem check021_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C020_rowCode 6*CFSGJankoTwoSelectedCaches02.C017_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C021_digit 6 j%5 := by decide +kernel

private theorem check021_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C020_rowCode 7*CFSGJankoTwoSelectedCaches02.C017_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C021_digit 7 j%5 := by decide +kernel

private theorem check021_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C020_rowCode 8*CFSGJankoTwoSelectedCaches02.C017_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C021_digit 8 j%5 := by decide +kernel

private theorem check021_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C020_rowCode 9*CFSGJankoTwoSelectedCaches02.C017_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C021_digit 9 j%5 := by decide +kernel

private theorem check021_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C020_rowCode 10*CFSGJankoTwoSelectedCaches02.C017_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C021_digit 10 j%5 := by decide +kernel

private theorem check021_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C020_rowCode 11*CFSGJankoTwoSelectedCaches02.C017_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C021_digit 11 j%5 := by decide +kernel

private theorem check021_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C020_rowCode 12*CFSGJankoTwoSelectedCaches02.C017_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C021_digit 12 j%5 := by decide +kernel

private theorem check021_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C020_rowCode 13*CFSGJankoTwoSelectedCaches02.C017_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C021_digit 13 j%5 := by decide +kernel

theorem checks021 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C020_rowCode i*CFSGJankoTwoSelectedCaches02.C017_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C021_digit i j%5 := by
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

theorem matrix_node021 : (node021 A B)=CFSGJankoTwoSelectedCaches03.C021_data.matrix 5 := by
  change (node020 A B)*(node017 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches02.C020_data CFSGJankoTwoSelectedCaches02.C017_data CFSGJankoTwoSelectedCaches03.C021_data
    CFSGJankoTwoSelectedProducts02.matrix_node020 CFSGJankoTwoSelectedProducts01.matrix_node017 (by decide : 14*(5-1)^2 < 256) checks021

private theorem check022_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 0*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C022_digit 0 j%5 := by decide +kernel

private theorem check022_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 1*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C022_digit 1 j%5 := by decide +kernel

private theorem check022_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 2*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C022_digit 2 j%5 := by decide +kernel

private theorem check022_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 3*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C022_digit 3 j%5 := by decide +kernel

private theorem check022_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 4*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C022_digit 4 j%5 := by decide +kernel

private theorem check022_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 5*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C022_digit 5 j%5 := by decide +kernel

private theorem check022_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 6*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C022_digit 6 j%5 := by decide +kernel

private theorem check022_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 7*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C022_digit 7 j%5 := by decide +kernel

private theorem check022_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 8*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C022_digit 8 j%5 := by decide +kernel

private theorem check022_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 9*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C022_digit 9 j%5 := by decide +kernel

private theorem check022_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 10*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C022_digit 10 j%5 := by decide +kernel

private theorem check022_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 11*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C022_digit 11 j%5 := by decide +kernel

private theorem check022_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 12*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C022_digit 12 j%5 := by decide +kernel

private theorem check022_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 13*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C022_digit 13 j%5 := by decide +kernel

theorem checks022 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode i*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C022_digit i j%5 := by
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

theorem matrix_node022 : (node022 A B)=CFSGJankoTwoSelectedCaches03.C022_data.matrix 5 := by
  change (node000 A B)*(node015 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches02.C015_data CFSGJankoTwoSelectedCaches03.C022_data
    CFSGJankoTwoSelectedBaseCaches.A_source_binding CFSGJankoTwoSelectedProducts01.matrix_node015 (by decide : 14*(5-1)^2 < 256) checks022

private theorem check023_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C022_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C023_digit 0 j%5 := by decide +kernel

private theorem check023_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C022_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C023_digit 1 j%5 := by decide +kernel

private theorem check023_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C022_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C023_digit 2 j%5 := by decide +kernel

private theorem check023_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C022_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C023_digit 3 j%5 := by decide +kernel

private theorem check023_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C022_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C023_digit 4 j%5 := by decide +kernel

private theorem check023_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C022_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C023_digit 5 j%5 := by decide +kernel

private theorem check023_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C022_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C023_digit 6 j%5 := by decide +kernel

private theorem check023_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C022_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C023_digit 7 j%5 := by decide +kernel

private theorem check023_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C022_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C023_digit 8 j%5 := by decide +kernel

private theorem check023_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C022_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C023_digit 9 j%5 := by decide +kernel

private theorem check023_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C022_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C023_digit 10 j%5 := by decide +kernel

private theorem check023_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C022_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C023_digit 11 j%5 := by decide +kernel

private theorem check023_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C022_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C023_digit 12 j%5 := by decide +kernel

private theorem check023_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C022_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C023_digit 13 j%5 := by decide +kernel

theorem checks023 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C022_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C023_digit i j%5 := by
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

theorem matrix_node023 : (node023 A B)=CFSGJankoTwoSelectedCaches03.C023_data.matrix 5 := by
  change (node022 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches03.C022_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches03.C023_data
    CFSGJankoTwoSelectedProducts02.matrix_node022 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks023

private theorem check024_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C023_rowCode 0*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C024_digit 0 j%5 := by decide +kernel

private theorem check024_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C023_rowCode 1*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C024_digit 1 j%5 := by decide +kernel

private theorem check024_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C023_rowCode 2*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C024_digit 2 j%5 := by decide +kernel

private theorem check024_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C023_rowCode 3*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C024_digit 3 j%5 := by decide +kernel

private theorem check024_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C023_rowCode 4*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C024_digit 4 j%5 := by decide +kernel

private theorem check024_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C023_rowCode 5*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C024_digit 5 j%5 := by decide +kernel

private theorem check024_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C023_rowCode 6*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C024_digit 6 j%5 := by decide +kernel

private theorem check024_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C023_rowCode 7*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C024_digit 7 j%5 := by decide +kernel

private theorem check024_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C023_rowCode 8*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C024_digit 8 j%5 := by decide +kernel

private theorem check024_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C023_rowCode 9*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C024_digit 9 j%5 := by decide +kernel

private theorem check024_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C023_rowCode 10*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C024_digit 10 j%5 := by decide +kernel

private theorem check024_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C023_rowCode 11*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C024_digit 11 j%5 := by decide +kernel

private theorem check024_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C023_rowCode 12*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C024_digit 12 j%5 := by decide +kernel

private theorem check024_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C023_rowCode 13*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C024_digit 13 j%5 := by decide +kernel

theorem checks024 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C023_rowCode i*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C024_digit i j%5 := by
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

theorem matrix_node024 : (node024 A B)=CFSGJankoTwoSelectedCaches03.C024_data.matrix 5 := by
  change (node023 A B)*(node015 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches03.C023_data CFSGJankoTwoSelectedCaches02.C015_data CFSGJankoTwoSelectedCaches03.C024_data
    CFSGJankoTwoSelectedProducts02.matrix_node023 CFSGJankoTwoSelectedProducts01.matrix_node015 (by decide : 14*(5-1)^2 < 256) checks024

private theorem check025_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C024_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C025_digit 0 j%5 := by decide +kernel

private theorem check025_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C024_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C025_digit 1 j%5 := by decide +kernel

private theorem check025_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C024_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C025_digit 2 j%5 := by decide +kernel

private theorem check025_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C024_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C025_digit 3 j%5 := by decide +kernel

private theorem check025_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C024_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C025_digit 4 j%5 := by decide +kernel

private theorem check025_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C024_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C025_digit 5 j%5 := by decide +kernel

private theorem check025_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C024_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C025_digit 6 j%5 := by decide +kernel

private theorem check025_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C024_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C025_digit 7 j%5 := by decide +kernel

private theorem check025_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C024_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C025_digit 8 j%5 := by decide +kernel

private theorem check025_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C024_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C025_digit 9 j%5 := by decide +kernel

private theorem check025_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C024_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C025_digit 10 j%5 := by decide +kernel

private theorem check025_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C024_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C025_digit 11 j%5 := by decide +kernel

private theorem check025_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C024_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C025_digit 12 j%5 := by decide +kernel

private theorem check025_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C024_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C025_digit 13 j%5 := by decide +kernel

theorem checks025 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C024_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C025_digit i j%5 := by
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

theorem matrix_node025 : (node025 A B)=CFSGJankoTwoSelectedCaches03.C025_data.matrix 5 := by
  change (node024 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches03.C024_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches03.C025_data
    CFSGJankoTwoSelectedProducts02.matrix_node024 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks025

private theorem check026_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C025_rowCode 0*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C026_digit 0 j%5 := by decide +kernel

private theorem check026_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C025_rowCode 1*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C026_digit 1 j%5 := by decide +kernel

private theorem check026_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C025_rowCode 2*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C026_digit 2 j%5 := by decide +kernel

private theorem check026_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C025_rowCode 3*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C026_digit 3 j%5 := by decide +kernel

private theorem check026_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C025_rowCode 4*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C026_digit 4 j%5 := by decide +kernel

private theorem check026_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C025_rowCode 5*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C026_digit 5 j%5 := by decide +kernel

private theorem check026_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C025_rowCode 6*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C026_digit 6 j%5 := by decide +kernel

private theorem check026_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C025_rowCode 7*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C026_digit 7 j%5 := by decide +kernel

private theorem check026_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C025_rowCode 8*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C026_digit 8 j%5 := by decide +kernel

private theorem check026_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C025_rowCode 9*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C026_digit 9 j%5 := by decide +kernel

private theorem check026_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C025_rowCode 10*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C026_digit 10 j%5 := by decide +kernel

private theorem check026_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C025_rowCode 11*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C026_digit 11 j%5 := by decide +kernel

private theorem check026_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C025_rowCode 12*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C026_digit 12 j%5 := by decide +kernel

private theorem check026_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C025_rowCode 13*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C026_digit 13 j%5 := by decide +kernel

theorem checks026 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches03.C025_rowCode i*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches03.C026_digit i j%5 := by
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

theorem matrix_node026 : (node026 A B)=CFSGJankoTwoSelectedCaches03.C026_data.matrix 5 := by
  change (node025 A B)*(node015 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches03.C025_data CFSGJankoTwoSelectedCaches02.C015_data CFSGJankoTwoSelectedCaches03.C026_data
    CFSGJankoTwoSelectedProducts02.matrix_node025 CFSGJankoTwoSelectedProducts01.matrix_node015 (by decide : 14*(5-1)^2 < 256) checks026

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts02
