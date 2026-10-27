import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedPositiveWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches00
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches01
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts00
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches02
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts01
open MatrixKroneckerProductReflection
open CFSGJankoTwoSelectedPositiveWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check011_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 0*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C011_digit 0 j%5 := by decide +kernel

private theorem check011_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 1*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C011_digit 1 j%5 := by decide +kernel

private theorem check011_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 2*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C011_digit 2 j%5 := by decide +kernel

private theorem check011_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 3*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C011_digit 3 j%5 := by decide +kernel

private theorem check011_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 4*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C011_digit 4 j%5 := by decide +kernel

private theorem check011_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 5*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C011_digit 5 j%5 := by decide +kernel

private theorem check011_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 6*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C011_digit 6 j%5 := by decide +kernel

private theorem check011_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 7*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C011_digit 7 j%5 := by decide +kernel

private theorem check011_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 8*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C011_digit 8 j%5 := by decide +kernel

private theorem check011_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 9*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C011_digit 9 j%5 := by decide +kernel

private theorem check011_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 10*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C011_digit 10 j%5 := by decide +kernel

private theorem check011_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 11*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C011_digit 11 j%5 := by decide +kernel

private theorem check011_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 12*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C011_digit 12 j%5 := by decide +kernel

private theorem check011_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 13*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C011_digit 13 j%5 := by decide +kernel

theorem checks011 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode i*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C011_digit i j%5 := by
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

theorem matrix_node011 : (node011 A B)=CFSGJankoTwoSelectedCaches01.C011_data.matrix 5 := by
  change (node008 A B)*(node008 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches00.C008_data CFSGJankoTwoSelectedCaches00.C008_data CFSGJankoTwoSelectedCaches01.C011_data
    CFSGJankoTwoSelectedProducts00.matrix_node008 CFSGJankoTwoSelectedProducts00.matrix_node008 (by decide : 14*(5-1)^2 < 256) checks011

private theorem check012_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C011_rowCode 0*CFSGJankoTwoSelectedCaches01.C011_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C012_digit 0 j%5 := by decide +kernel

private theorem check012_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C011_rowCode 1*CFSGJankoTwoSelectedCaches01.C011_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C012_digit 1 j%5 := by decide +kernel

private theorem check012_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C011_rowCode 2*CFSGJankoTwoSelectedCaches01.C011_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C012_digit 2 j%5 := by decide +kernel

private theorem check012_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C011_rowCode 3*CFSGJankoTwoSelectedCaches01.C011_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C012_digit 3 j%5 := by decide +kernel

private theorem check012_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C011_rowCode 4*CFSGJankoTwoSelectedCaches01.C011_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C012_digit 4 j%5 := by decide +kernel

private theorem check012_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C011_rowCode 5*CFSGJankoTwoSelectedCaches01.C011_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C012_digit 5 j%5 := by decide +kernel

private theorem check012_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C011_rowCode 6*CFSGJankoTwoSelectedCaches01.C011_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C012_digit 6 j%5 := by decide +kernel

private theorem check012_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C011_rowCode 7*CFSGJankoTwoSelectedCaches01.C011_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C012_digit 7 j%5 := by decide +kernel

private theorem check012_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C011_rowCode 8*CFSGJankoTwoSelectedCaches01.C011_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C012_digit 8 j%5 := by decide +kernel

private theorem check012_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C011_rowCode 9*CFSGJankoTwoSelectedCaches01.C011_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C012_digit 9 j%5 := by decide +kernel

private theorem check012_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C011_rowCode 10*CFSGJankoTwoSelectedCaches01.C011_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C012_digit 10 j%5 := by decide +kernel

private theorem check012_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C011_rowCode 11*CFSGJankoTwoSelectedCaches01.C011_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C012_digit 11 j%5 := by decide +kernel

private theorem check012_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C011_rowCode 12*CFSGJankoTwoSelectedCaches01.C011_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C012_digit 12 j%5 := by decide +kernel

private theorem check012_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C011_rowCode 13*CFSGJankoTwoSelectedCaches01.C011_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C012_digit 13 j%5 := by decide +kernel

theorem checks012 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C011_rowCode i*CFSGJankoTwoSelectedCaches01.C011_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C012_digit i j%5 := by
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

theorem matrix_node012 : (node012 A B)=CFSGJankoTwoSelectedCaches01.C012_data.matrix 5 := by
  change (node011 A B)*(node011 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches01.C011_data CFSGJankoTwoSelectedCaches01.C011_data CFSGJankoTwoSelectedCaches01.C012_data
    CFSGJankoTwoSelectedProducts01.matrix_node011 CFSGJankoTwoSelectedProducts01.matrix_node011 (by decide : 14*(5-1)^2 < 256) checks012

private theorem check013_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 0*CFSGJankoTwoSelectedCaches01.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C013_digit 0 j%5 := by decide +kernel

private theorem check013_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 1*CFSGJankoTwoSelectedCaches01.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C013_digit 1 j%5 := by decide +kernel

private theorem check013_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 2*CFSGJankoTwoSelectedCaches01.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C013_digit 2 j%5 := by decide +kernel

private theorem check013_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 3*CFSGJankoTwoSelectedCaches01.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C013_digit 3 j%5 := by decide +kernel

private theorem check013_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 4*CFSGJankoTwoSelectedCaches01.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C013_digit 4 j%5 := by decide +kernel

private theorem check013_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 5*CFSGJankoTwoSelectedCaches01.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C013_digit 5 j%5 := by decide +kernel

private theorem check013_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 6*CFSGJankoTwoSelectedCaches01.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C013_digit 6 j%5 := by decide +kernel

private theorem check013_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 7*CFSGJankoTwoSelectedCaches01.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C013_digit 7 j%5 := by decide +kernel

private theorem check013_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 8*CFSGJankoTwoSelectedCaches01.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C013_digit 8 j%5 := by decide +kernel

private theorem check013_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 9*CFSGJankoTwoSelectedCaches01.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C013_digit 9 j%5 := by decide +kernel

private theorem check013_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 10*CFSGJankoTwoSelectedCaches01.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C013_digit 10 j%5 := by decide +kernel

private theorem check013_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 11*CFSGJankoTwoSelectedCaches01.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C013_digit 11 j%5 := by decide +kernel

private theorem check013_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 12*CFSGJankoTwoSelectedCaches01.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C013_digit 12 j%5 := by decide +kernel

private theorem check013_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode 13*CFSGJankoTwoSelectedCaches01.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C013_digit 13 j%5 := by decide +kernel

theorem checks013 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C008_rowCode i*CFSGJankoTwoSelectedCaches01.C012_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C013_digit i j%5 := by
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

theorem matrix_node013 : (node013 A B)=CFSGJankoTwoSelectedCaches01.C013_data.matrix 5 := by
  change (node008 A B)*(node012 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches00.C008_data CFSGJankoTwoSelectedCaches01.C012_data CFSGJankoTwoSelectedCaches01.C013_data
    CFSGJankoTwoSelectedProducts00.matrix_node008 CFSGJankoTwoSelectedProducts01.matrix_node012 (by decide : 14*(5-1)^2 < 256) checks013

private theorem check014_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C013_rowCode 0*CFSGJankoTwoSelectedCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C014_digit 0 j%5 := by decide +kernel

private theorem check014_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C013_rowCode 1*CFSGJankoTwoSelectedCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C014_digit 1 j%5 := by decide +kernel

private theorem check014_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C013_rowCode 2*CFSGJankoTwoSelectedCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C014_digit 2 j%5 := by decide +kernel

private theorem check014_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C013_rowCode 3*CFSGJankoTwoSelectedCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C014_digit 3 j%5 := by decide +kernel

private theorem check014_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C013_rowCode 4*CFSGJankoTwoSelectedCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C014_digit 4 j%5 := by decide +kernel

private theorem check014_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C013_rowCode 5*CFSGJankoTwoSelectedCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C014_digit 5 j%5 := by decide +kernel

private theorem check014_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C013_rowCode 6*CFSGJankoTwoSelectedCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C014_digit 6 j%5 := by decide +kernel

private theorem check014_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C013_rowCode 7*CFSGJankoTwoSelectedCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C014_digit 7 j%5 := by decide +kernel

private theorem check014_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C013_rowCode 8*CFSGJankoTwoSelectedCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C014_digit 8 j%5 := by decide +kernel

private theorem check014_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C013_rowCode 9*CFSGJankoTwoSelectedCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C014_digit 9 j%5 := by decide +kernel

private theorem check014_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C013_rowCode 10*CFSGJankoTwoSelectedCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C014_digit 10 j%5 := by decide +kernel

private theorem check014_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C013_rowCode 11*CFSGJankoTwoSelectedCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C014_digit 11 j%5 := by decide +kernel

private theorem check014_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C013_rowCode 12*CFSGJankoTwoSelectedCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C014_digit 12 j%5 := by decide +kernel

private theorem check014_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C013_rowCode 13*CFSGJankoTwoSelectedCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C014_digit 13 j%5 := by decide +kernel

theorem checks014 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C013_rowCode i*CFSGJankoTwoSelectedCaches01.C010_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches01.C014_digit i j%5 := by
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

theorem matrix_node014 : (node014 A B)=CFSGJankoTwoSelectedCaches01.C014_data.matrix 5 := by
  change (node013 A B)*(node010 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches01.C013_data CFSGJankoTwoSelectedCaches01.C010_data CFSGJankoTwoSelectedCaches01.C014_data
    CFSGJankoTwoSelectedProducts01.matrix_node013 CFSGJankoTwoSelectedProducts00.matrix_node010 (by decide : 14*(5-1)^2 < 256) checks014

private theorem check015_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C014_rowCode 0*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C015_digit 0 j%5 := by decide +kernel

private theorem check015_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C014_rowCode 1*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C015_digit 1 j%5 := by decide +kernel

private theorem check015_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C014_rowCode 2*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C015_digit 2 j%5 := by decide +kernel

private theorem check015_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C014_rowCode 3*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C015_digit 3 j%5 := by decide +kernel

private theorem check015_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C014_rowCode 4*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C015_digit 4 j%5 := by decide +kernel

private theorem check015_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C014_rowCode 5*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C015_digit 5 j%5 := by decide +kernel

private theorem check015_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C014_rowCode 6*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C015_digit 6 j%5 := by decide +kernel

private theorem check015_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C014_rowCode 7*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C015_digit 7 j%5 := by decide +kernel

private theorem check015_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C014_rowCode 8*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C015_digit 8 j%5 := by decide +kernel

private theorem check015_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C014_rowCode 9*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C015_digit 9 j%5 := by decide +kernel

private theorem check015_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C014_rowCode 10*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C015_digit 10 j%5 := by decide +kernel

private theorem check015_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C014_rowCode 11*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C015_digit 11 j%5 := by decide +kernel

private theorem check015_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C014_rowCode 12*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C015_digit 12 j%5 := by decide +kernel

private theorem check015_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C014_rowCode 13*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C015_digit 13 j%5 := by decide +kernel

theorem checks015 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches01.C014_rowCode i*CFSGJankoTwoSelectedCaches00.C008_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C015_digit i j%5 := by
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

theorem matrix_node015 : (node015 A B)=CFSGJankoTwoSelectedCaches02.C015_data.matrix 5 := by
  change (node014 A B)*(node008 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches01.C014_data CFSGJankoTwoSelectedCaches00.C008_data CFSGJankoTwoSelectedCaches02.C015_data
    CFSGJankoTwoSelectedProducts01.matrix_node014 CFSGJankoTwoSelectedProducts00.matrix_node008 (by decide : 14*(5-1)^2 < 256) checks015

private theorem check016_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 0*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 0 j%5 := by decide +kernel

private theorem check016_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 1*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 1 j%5 := by decide +kernel

private theorem check016_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 2*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 2 j%5 := by decide +kernel

private theorem check016_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 3*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 3 j%5 := by decide +kernel

private theorem check016_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 4*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 4 j%5 := by decide +kernel

private theorem check016_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 5*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 5 j%5 := by decide +kernel

private theorem check016_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 6*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 6 j%5 := by decide +kernel

private theorem check016_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 7*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 7 j%5 := by decide +kernel

private theorem check016_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 8*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 8 j%5 := by decide +kernel

private theorem check016_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 9*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 9 j%5 := by decide +kernel

private theorem check016_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 10*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 10 j%5 := by decide +kernel

private theorem check016_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 11*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 11 j%5 := by decide +kernel

private theorem check016_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 12*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 12 j%5 := by decide +kernel

private theorem check016_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 13*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit 13 j%5 := by decide +kernel

theorem checks016 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode i*CFSGJankoTwoSelectedCaches02.C015_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C016_digit i j%5 := by
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

theorem matrix_node016 : (node016 A B)=CFSGJankoTwoSelectedCaches02.C016_data.matrix 5 := by
  change (node015 A B)*(node015 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches02.C015_data CFSGJankoTwoSelectedCaches02.C015_data CFSGJankoTwoSelectedCaches02.C016_data
    CFSGJankoTwoSelectedProducts01.matrix_node015 CFSGJankoTwoSelectedProducts01.matrix_node015 (by decide : 14*(5-1)^2 < 256) checks016

private theorem check017_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 0*CFSGJankoTwoSelectedCaches02.C016_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C017_digit 0 j%5 := by decide +kernel

private theorem check017_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 1*CFSGJankoTwoSelectedCaches02.C016_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C017_digit 1 j%5 := by decide +kernel

private theorem check017_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 2*CFSGJankoTwoSelectedCaches02.C016_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C017_digit 2 j%5 := by decide +kernel

private theorem check017_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 3*CFSGJankoTwoSelectedCaches02.C016_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C017_digit 3 j%5 := by decide +kernel

private theorem check017_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 4*CFSGJankoTwoSelectedCaches02.C016_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C017_digit 4 j%5 := by decide +kernel

private theorem check017_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 5*CFSGJankoTwoSelectedCaches02.C016_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C017_digit 5 j%5 := by decide +kernel

private theorem check017_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 6*CFSGJankoTwoSelectedCaches02.C016_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C017_digit 6 j%5 := by decide +kernel

private theorem check017_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 7*CFSGJankoTwoSelectedCaches02.C016_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C017_digit 7 j%5 := by decide +kernel

private theorem check017_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 8*CFSGJankoTwoSelectedCaches02.C016_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C017_digit 8 j%5 := by decide +kernel

private theorem check017_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 9*CFSGJankoTwoSelectedCaches02.C016_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C017_digit 9 j%5 := by decide +kernel

private theorem check017_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 10*CFSGJankoTwoSelectedCaches02.C016_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C017_digit 10 j%5 := by decide +kernel

private theorem check017_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 11*CFSGJankoTwoSelectedCaches02.C016_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C017_digit 11 j%5 := by decide +kernel

private theorem check017_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 12*CFSGJankoTwoSelectedCaches02.C016_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C017_digit 12 j%5 := by decide +kernel

private theorem check017_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode 13*CFSGJankoTwoSelectedCaches02.C016_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C017_digit 13 j%5 := by decide +kernel

theorem checks017 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C015_rowCode i*CFSGJankoTwoSelectedCaches02.C016_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C017_digit i j%5 := by
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

theorem matrix_node017 : (node017 A B)=CFSGJankoTwoSelectedCaches02.C017_data.matrix 5 := by
  change (node015 A B)*(node016 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches02.C015_data CFSGJankoTwoSelectedCaches02.C016_data CFSGJankoTwoSelectedCaches02.C017_data
    CFSGJankoTwoSelectedProducts01.matrix_node015 CFSGJankoTwoSelectedProducts01.matrix_node016 (by decide : 14*(5-1)^2 < 256) checks017

private theorem check018_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C017_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C018_digit 0 j%5 := by decide +kernel

private theorem check018_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C017_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C018_digit 1 j%5 := by decide +kernel

private theorem check018_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C017_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C018_digit 2 j%5 := by decide +kernel

private theorem check018_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C017_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C018_digit 3 j%5 := by decide +kernel

private theorem check018_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C017_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C018_digit 4 j%5 := by decide +kernel

private theorem check018_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C017_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C018_digit 5 j%5 := by decide +kernel

private theorem check018_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C017_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C018_digit 6 j%5 := by decide +kernel

private theorem check018_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C017_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C018_digit 7 j%5 := by decide +kernel

private theorem check018_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C017_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C018_digit 8 j%5 := by decide +kernel

private theorem check018_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C017_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C018_digit 9 j%5 := by decide +kernel

private theorem check018_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C017_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C018_digit 10 j%5 := by decide +kernel

private theorem check018_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C017_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C018_digit 11 j%5 := by decide +kernel

private theorem check018_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C017_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C018_digit 12 j%5 := by decide +kernel

private theorem check018_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C017_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C018_digit 13 j%5 := by decide +kernel

theorem checks018 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches02.C017_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches02.C018_digit i j%5 := by
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

theorem matrix_node018 : (node018 A B)=CFSGJankoTwoSelectedCaches02.C018_data.matrix 5 := by
  change (node017 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches02.C017_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches02.C018_data
    CFSGJankoTwoSelectedProducts01.matrix_node017 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks018

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts01
