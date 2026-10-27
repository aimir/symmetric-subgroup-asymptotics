import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedPositiveWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches07
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches11
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts07
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches10
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts10
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts11
open MatrixKroneckerProductReflection
open CFSGJankoTwoSelectedPositiveWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check095_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C070_rowCode 0*CFSGJankoTwoSelectedCaches07.C070_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C095_digit 0 j%5 := by decide +kernel

private theorem check095_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C070_rowCode 1*CFSGJankoTwoSelectedCaches07.C070_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C095_digit 1 j%5 := by decide +kernel

private theorem check095_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C070_rowCode 2*CFSGJankoTwoSelectedCaches07.C070_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C095_digit 2 j%5 := by decide +kernel

private theorem check095_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C070_rowCode 3*CFSGJankoTwoSelectedCaches07.C070_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C095_digit 3 j%5 := by decide +kernel

private theorem check095_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C070_rowCode 4*CFSGJankoTwoSelectedCaches07.C070_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C095_digit 4 j%5 := by decide +kernel

private theorem check095_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C070_rowCode 5*CFSGJankoTwoSelectedCaches07.C070_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C095_digit 5 j%5 := by decide +kernel

private theorem check095_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C070_rowCode 6*CFSGJankoTwoSelectedCaches07.C070_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C095_digit 6 j%5 := by decide +kernel

private theorem check095_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C070_rowCode 7*CFSGJankoTwoSelectedCaches07.C070_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C095_digit 7 j%5 := by decide +kernel

private theorem check095_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C070_rowCode 8*CFSGJankoTwoSelectedCaches07.C070_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C095_digit 8 j%5 := by decide +kernel

private theorem check095_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C070_rowCode 9*CFSGJankoTwoSelectedCaches07.C070_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C095_digit 9 j%5 := by decide +kernel

private theorem check095_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C070_rowCode 10*CFSGJankoTwoSelectedCaches07.C070_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C095_digit 10 j%5 := by decide +kernel

private theorem check095_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C070_rowCode 11*CFSGJankoTwoSelectedCaches07.C070_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C095_digit 11 j%5 := by decide +kernel

private theorem check095_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C070_rowCode 12*CFSGJankoTwoSelectedCaches07.C070_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C095_digit 12 j%5 := by decide +kernel

private theorem check095_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C070_rowCode 13*CFSGJankoTwoSelectedCaches07.C070_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C095_digit 13 j%5 := by decide +kernel

theorem checks095 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C070_rowCode i*CFSGJankoTwoSelectedCaches07.C070_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C095_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check095_00 j
  · exact check095_01 j
  · exact check095_02 j
  · exact check095_03 j
  · exact check095_04 j
  · exact check095_05 j
  · exact check095_06 j
  · exact check095_07 j
  · exact check095_08 j
  · exact check095_09 j
  · exact check095_10 j
  · exact check095_11 j
  · exact check095_12 j
  · exact check095_13 j

theorem matrix_node095 : (node095 A B)=CFSGJankoTwoSelectedCaches11.C095_data.matrix 5 := by
  change (node070 A B)*(node070 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches07.C070_data CFSGJankoTwoSelectedCaches07.C070_data CFSGJankoTwoSelectedCaches11.C095_data
    CFSGJankoTwoSelectedProducts07.matrix_node070 CFSGJankoTwoSelectedProducts07.matrix_node070 (by decide : 14*(5-1)^2 < 256) checks095

private theorem check096_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C095_rowCode 0*CFSGJankoTwoSelectedCaches11.C095_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 0 j%5 := by decide +kernel

private theorem check096_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C095_rowCode 1*CFSGJankoTwoSelectedCaches11.C095_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 1 j%5 := by decide +kernel

private theorem check096_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C095_rowCode 2*CFSGJankoTwoSelectedCaches11.C095_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 2 j%5 := by decide +kernel

private theorem check096_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C095_rowCode 3*CFSGJankoTwoSelectedCaches11.C095_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 3 j%5 := by decide +kernel

private theorem check096_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C095_rowCode 4*CFSGJankoTwoSelectedCaches11.C095_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 4 j%5 := by decide +kernel

private theorem check096_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C095_rowCode 5*CFSGJankoTwoSelectedCaches11.C095_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 5 j%5 := by decide +kernel

private theorem check096_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C095_rowCode 6*CFSGJankoTwoSelectedCaches11.C095_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 6 j%5 := by decide +kernel

private theorem check096_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C095_rowCode 7*CFSGJankoTwoSelectedCaches11.C095_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 7 j%5 := by decide +kernel

private theorem check096_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C095_rowCode 8*CFSGJankoTwoSelectedCaches11.C095_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 8 j%5 := by decide +kernel

private theorem check096_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C095_rowCode 9*CFSGJankoTwoSelectedCaches11.C095_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 9 j%5 := by decide +kernel

private theorem check096_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C095_rowCode 10*CFSGJankoTwoSelectedCaches11.C095_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 10 j%5 := by decide +kernel

private theorem check096_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C095_rowCode 11*CFSGJankoTwoSelectedCaches11.C095_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 11 j%5 := by decide +kernel

private theorem check096_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C095_rowCode 12*CFSGJankoTwoSelectedCaches11.C095_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 12 j%5 := by decide +kernel

private theorem check096_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C095_rowCode 13*CFSGJankoTwoSelectedCaches11.C095_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 13 j%5 := by decide +kernel

theorem checks096 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C095_rowCode i*CFSGJankoTwoSelectedCaches11.C095_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check096_00 j
  · exact check096_01 j
  · exact check096_02 j
  · exact check096_03 j
  · exact check096_04 j
  · exact check096_05 j
  · exact check096_06 j
  · exact check096_07 j
  · exact check096_08 j
  · exact check096_09 j
  · exact check096_10 j
  · exact check096_11 j
  · exact check096_12 j
  · exact check096_13 j

theorem matrix_node096 : (node096 A B)=CFSGJankoTwoSelectedCaches11.C096_data.matrix 5 := by
  change (node095 A B)*(node095 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches11.C095_data CFSGJankoTwoSelectedCaches11.C095_data CFSGJankoTwoSelectedCaches11.C096_data
    CFSGJankoTwoSelectedProducts11.matrix_node095 CFSGJankoTwoSelectedProducts11.matrix_node095 (by decide : 14*(5-1)^2 < 256) checks096

private theorem check097_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 0*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 0 j%5 := by decide +kernel

private theorem check097_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 1*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 1 j%5 := by decide +kernel

private theorem check097_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 2*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 2 j%5 := by decide +kernel

private theorem check097_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 3*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 3 j%5 := by decide +kernel

private theorem check097_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 4*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 4 j%5 := by decide +kernel

private theorem check097_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 5*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 5 j%5 := by decide +kernel

private theorem check097_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 6*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 6 j%5 := by decide +kernel

private theorem check097_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 7*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 7 j%5 := by decide +kernel

private theorem check097_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 8*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 8 j%5 := by decide +kernel

private theorem check097_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 9*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 9 j%5 := by decide +kernel

private theorem check097_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 10*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 10 j%5 := by decide +kernel

private theorem check097_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 11*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 11 j%5 := by decide +kernel

private theorem check097_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 12*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 12 j%5 := by decide +kernel

private theorem check097_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 13*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit 13 j%5 := by decide +kernel

theorem checks097 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode i*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C096_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check097_00 j
  · exact check097_01 j
  · exact check097_02 j
  · exact check097_03 j
  · exact check097_04 j
  · exact check097_05 j
  · exact check097_06 j
  · exact check097_07 j
  · exact check097_08 j
  · exact check097_09 j
  · exact check097_10 j
  · exact check097_11 j
  · exact check097_12 j
  · exact check097_13 j

theorem matrix_node097 : (node097 A B)=CFSGJankoTwoSelectedCaches11.C096_data.matrix 5 := by
  change (node002 A B)*(node096 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedBaseCaches.I_data CFSGJankoTwoSelectedCaches11.C096_data CFSGJankoTwoSelectedCaches11.C096_data
    (show (1 : Matrix (Fin 14) (Fin 14) (ZMod 5))=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 from CFSGJankoTwoSelectedBaseCaches.identity_binding.symm) CFSGJankoTwoSelectedProducts11.matrix_node096 (by decide : 14*(5-1)^2 < 256) checks097

private theorem check098_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 0*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C098_digit 0 j%5 := by decide +kernel

private theorem check098_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 1*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C098_digit 1 j%5 := by decide +kernel

private theorem check098_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 2*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C098_digit 2 j%5 := by decide +kernel

private theorem check098_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 3*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C098_digit 3 j%5 := by decide +kernel

private theorem check098_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 4*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C098_digit 4 j%5 := by decide +kernel

private theorem check098_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 5*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C098_digit 5 j%5 := by decide +kernel

private theorem check098_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 6*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C098_digit 6 j%5 := by decide +kernel

private theorem check098_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 7*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C098_digit 7 j%5 := by decide +kernel

private theorem check098_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 8*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C098_digit 8 j%5 := by decide +kernel

private theorem check098_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 9*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C098_digit 9 j%5 := by decide +kernel

private theorem check098_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 10*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C098_digit 10 j%5 := by decide +kernel

private theorem check098_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 11*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C098_digit 11 j%5 := by decide +kernel

private theorem check098_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 12*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C098_digit 12 j%5 := by decide +kernel

private theorem check098_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 13*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C098_digit 13 j%5 := by decide +kernel

theorem checks098 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode i*CFSGJankoTwoSelectedCaches11.C096_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C098_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check098_00 j
  · exact check098_01 j
  · exact check098_02 j
  · exact check098_03 j
  · exact check098_04 j
  · exact check098_05 j
  · exact check098_06 j
  · exact check098_07 j
  · exact check098_08 j
  · exact check098_09 j
  · exact check098_10 j
  · exact check098_11 j
  · exact check098_12 j
  · exact check098_13 j

theorem matrix_node098 : (node098 A B)=CFSGJankoTwoSelectedCaches11.C098_data.matrix 5 := by
  change (node096 A B)*(node096 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches11.C096_data CFSGJankoTwoSelectedCaches11.C096_data CFSGJankoTwoSelectedCaches11.C098_data
    CFSGJankoTwoSelectedProducts11.matrix_node096 CFSGJankoTwoSelectedProducts11.matrix_node096 (by decide : 14*(5-1)^2 < 256) checks098

private theorem check099_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 0*CFSGJankoTwoSelectedCaches11.C098_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 0 j%5 := by decide +kernel

private theorem check099_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 1*CFSGJankoTwoSelectedCaches11.C098_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 1 j%5 := by decide +kernel

private theorem check099_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 2*CFSGJankoTwoSelectedCaches11.C098_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 2 j%5 := by decide +kernel

private theorem check099_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 3*CFSGJankoTwoSelectedCaches11.C098_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 3 j%5 := by decide +kernel

private theorem check099_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 4*CFSGJankoTwoSelectedCaches11.C098_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 4 j%5 := by decide +kernel

private theorem check099_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 5*CFSGJankoTwoSelectedCaches11.C098_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 5 j%5 := by decide +kernel

private theorem check099_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 6*CFSGJankoTwoSelectedCaches11.C098_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 6 j%5 := by decide +kernel

private theorem check099_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 7*CFSGJankoTwoSelectedCaches11.C098_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 7 j%5 := by decide +kernel

private theorem check099_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 8*CFSGJankoTwoSelectedCaches11.C098_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 8 j%5 := by decide +kernel

private theorem check099_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 9*CFSGJankoTwoSelectedCaches11.C098_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 9 j%5 := by decide +kernel

private theorem check099_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 10*CFSGJankoTwoSelectedCaches11.C098_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 10 j%5 := by decide +kernel

private theorem check099_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 11*CFSGJankoTwoSelectedCaches11.C098_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 11 j%5 := by decide +kernel

private theorem check099_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 12*CFSGJankoTwoSelectedCaches11.C098_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 12 j%5 := by decide +kernel

private theorem check099_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode 13*CFSGJankoTwoSelectedCaches11.C098_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 13 j%5 := by decide +kernel

theorem checks099 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches11.C096_rowCode i*CFSGJankoTwoSelectedCaches11.C098_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check099_00 j
  · exact check099_01 j
  · exact check099_02 j
  · exact check099_03 j
  · exact check099_04 j
  · exact check099_05 j
  · exact check099_06 j
  · exact check099_07 j
  · exact check099_08 j
  · exact check099_09 j
  · exact check099_10 j
  · exact check099_11 j
  · exact check099_12 j
  · exact check099_13 j

theorem matrix_node099 : (node099 A B)=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 := by
  change (node097 A B)*(node098 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches11.C096_data CFSGJankoTwoSelectedCaches11.C098_data CFSGJankoTwoSelectedBaseCaches.I_data
    CFSGJankoTwoSelectedProducts11.matrix_node097 CFSGJankoTwoSelectedProducts11.matrix_node098 (by decide : 14*(5-1)^2 < 256) checks099

private theorem check100_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 0*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 0 j%5 := by decide +kernel

private theorem check100_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 1*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 1 j%5 := by decide +kernel

private theorem check100_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 2*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 2 j%5 := by decide +kernel

private theorem check100_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 3*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 3 j%5 := by decide +kernel

private theorem check100_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 4*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 4 j%5 := by decide +kernel

private theorem check100_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 5*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 5 j%5 := by decide +kernel

private theorem check100_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 6*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 6 j%5 := by decide +kernel

private theorem check100_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 7*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 7 j%5 := by decide +kernel

private theorem check100_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 8*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 8 j%5 := by decide +kernel

private theorem check100_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 9*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 9 j%5 := by decide +kernel

private theorem check100_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 10*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 10 j%5 := by decide +kernel

private theorem check100_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 11*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 11 j%5 := by decide +kernel

private theorem check100_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 12*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 12 j%5 := by decide +kernel

private theorem check100_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 13*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit 13 j%5 := by decide +kernel

theorem checks100 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode i*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches10.C094_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check100_00 j
  · exact check100_01 j
  · exact check100_02 j
  · exact check100_03 j
  · exact check100_04 j
  · exact check100_05 j
  · exact check100_06 j
  · exact check100_07 j
  · exact check100_08 j
  · exact check100_09 j
  · exact check100_10 j
  · exact check100_11 j
  · exact check100_12 j
  · exact check100_13 j

theorem matrix_node100 : (node100 A B)=CFSGJankoTwoSelectedCaches10.C094_data.matrix 5 := by
  change (node002 A B)*(node094 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedBaseCaches.I_data CFSGJankoTwoSelectedCaches10.C094_data CFSGJankoTwoSelectedCaches10.C094_data
    (show (1 : Matrix (Fin 14) (Fin 14) (ZMod 5))=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 from CFSGJankoTwoSelectedBaseCaches.identity_binding.symm) CFSGJankoTwoSelectedProducts10.matrix_node094 (by decide : 14*(5-1)^2 < 256) checks100

private theorem check101_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 0*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C101_digit 0 j%5 := by decide +kernel

private theorem check101_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 1*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C101_digit 1 j%5 := by decide +kernel

private theorem check101_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 2*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C101_digit 2 j%5 := by decide +kernel

private theorem check101_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 3*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C101_digit 3 j%5 := by decide +kernel

private theorem check101_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 4*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C101_digit 4 j%5 := by decide +kernel

private theorem check101_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 5*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C101_digit 5 j%5 := by decide +kernel

private theorem check101_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 6*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C101_digit 6 j%5 := by decide +kernel

private theorem check101_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 7*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C101_digit 7 j%5 := by decide +kernel

private theorem check101_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 8*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C101_digit 8 j%5 := by decide +kernel

private theorem check101_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 9*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C101_digit 9 j%5 := by decide +kernel

private theorem check101_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 10*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C101_digit 10 j%5 := by decide +kernel

private theorem check101_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 11*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C101_digit 11 j%5 := by decide +kernel

private theorem check101_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 12*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C101_digit 12 j%5 := by decide +kernel

private theorem check101_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 13*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C101_digit 13 j%5 := by decide +kernel

theorem checks101 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode i*CFSGJankoTwoSelectedCaches10.C094_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches11.C101_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check101_00 j
  · exact check101_01 j
  · exact check101_02 j
  · exact check101_03 j
  · exact check101_04 j
  · exact check101_05 j
  · exact check101_06 j
  · exact check101_07 j
  · exact check101_08 j
  · exact check101_09 j
  · exact check101_10 j
  · exact check101_11 j
  · exact check101_12 j
  · exact check101_13 j

theorem matrix_node101 : (node101 A B)=CFSGJankoTwoSelectedCaches11.C101_data.matrix 5 := by
  change (node094 A B)*(node094 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches10.C094_data CFSGJankoTwoSelectedCaches10.C094_data CFSGJankoTwoSelectedCaches11.C101_data
    CFSGJankoTwoSelectedProducts10.matrix_node094 CFSGJankoTwoSelectedProducts10.matrix_node094 (by decide : 14*(5-1)^2 < 256) checks101

private theorem check102_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 0*CFSGJankoTwoSelectedCaches11.C101_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 0 j%5 := by decide +kernel

private theorem check102_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 1*CFSGJankoTwoSelectedCaches11.C101_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 1 j%5 := by decide +kernel

private theorem check102_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 2*CFSGJankoTwoSelectedCaches11.C101_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 2 j%5 := by decide +kernel

private theorem check102_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 3*CFSGJankoTwoSelectedCaches11.C101_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 3 j%5 := by decide +kernel

private theorem check102_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 4*CFSGJankoTwoSelectedCaches11.C101_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 4 j%5 := by decide +kernel

private theorem check102_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 5*CFSGJankoTwoSelectedCaches11.C101_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 5 j%5 := by decide +kernel

private theorem check102_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 6*CFSGJankoTwoSelectedCaches11.C101_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 6 j%5 := by decide +kernel

private theorem check102_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 7*CFSGJankoTwoSelectedCaches11.C101_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 7 j%5 := by decide +kernel

private theorem check102_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 8*CFSGJankoTwoSelectedCaches11.C101_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 8 j%5 := by decide +kernel

private theorem check102_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 9*CFSGJankoTwoSelectedCaches11.C101_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 9 j%5 := by decide +kernel

private theorem check102_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 10*CFSGJankoTwoSelectedCaches11.C101_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 10 j%5 := by decide +kernel

private theorem check102_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 11*CFSGJankoTwoSelectedCaches11.C101_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 11 j%5 := by decide +kernel

private theorem check102_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 12*CFSGJankoTwoSelectedCaches11.C101_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 12 j%5 := by decide +kernel

private theorem check102_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode 13*CFSGJankoTwoSelectedCaches11.C101_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 13 j%5 := by decide +kernel

theorem checks102 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches10.C094_rowCode i*CFSGJankoTwoSelectedCaches11.C101_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check102_00 j
  · exact check102_01 j
  · exact check102_02 j
  · exact check102_03 j
  · exact check102_04 j
  · exact check102_05 j
  · exact check102_06 j
  · exact check102_07 j
  · exact check102_08 j
  · exact check102_09 j
  · exact check102_10 j
  · exact check102_11 j
  · exact check102_12 j
  · exact check102_13 j

theorem matrix_node102 : (node102 A B)=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 := by
  change (node100 A B)*(node101 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches10.C094_data CFSGJankoTwoSelectedCaches11.C101_data CFSGJankoTwoSelectedBaseCaches.I_data
    CFSGJankoTwoSelectedProducts11.matrix_node100 CFSGJankoTwoSelectedProducts11.matrix_node101 (by decide : 14*(5-1)^2 < 256) checks102

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts11
