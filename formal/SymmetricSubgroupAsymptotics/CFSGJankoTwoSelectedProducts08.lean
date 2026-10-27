import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedPositiveWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches00
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches07
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches06
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedSeedPowerPilot
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches08
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts08
open MatrixKroneckerProductReflection
open CFSGJankoTwoSelectedPositiveWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check071_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 0 j%5 := by decide +kernel

private theorem check071_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 1 j%5 := by decide +kernel

private theorem check071_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 2 j%5 := by decide +kernel

private theorem check071_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 3 j%5 := by decide +kernel

private theorem check071_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 4 j%5 := by decide +kernel

private theorem check071_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 5 j%5 := by decide +kernel

private theorem check071_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 6 j%5 := by decide +kernel

private theorem check071_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 7 j%5 := by decide +kernel

private theorem check071_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 8 j%5 := by decide +kernel

private theorem check071_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 9 j%5 := by decide +kernel

private theorem check071_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 10 j%5 := by decide +kernel

private theorem check071_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 11 j%5 := by decide +kernel

private theorem check071_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 12 j%5 := by decide +kernel

private theorem check071_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 13 j%5 := by decide +kernel

theorem checks071 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check071_00 j
  · exact check071_01 j
  · exact check071_02 j
  · exact check071_03 j
  · exact check071_04 j
  · exact check071_05 j
  · exact check071_06 j
  · exact check071_07 j
  · exact check071_08 j
  · exact check071_09 j
  · exact check071_10 j
  · exact check071_11 j
  · exact check071_12 j
  · exact check071_13 j

theorem matrix_node071 : (node071 A B)=CFSGJankoTwoSelectedBaseCaches.A_data.matrix 5 := by
  change (node002 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedBaseCaches.I_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedBaseCaches.A_data
    (show (1 : Matrix (Fin 14) (Fin 14) (ZMod 5))=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 from CFSGJankoTwoSelectedBaseCaches.identity_binding.symm) CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks071

private theorem check072_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 0*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 0 j%5 := by decide +kernel

private theorem check072_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 1*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 1 j%5 := by decide +kernel

private theorem check072_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 2*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 2 j%5 := by decide +kernel

private theorem check072_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 3*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 3 j%5 := by decide +kernel

private theorem check072_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 4*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 4 j%5 := by decide +kernel

private theorem check072_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 5*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 5 j%5 := by decide +kernel

private theorem check072_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 6*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 6 j%5 := by decide +kernel

private theorem check072_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 7*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 7 j%5 := by decide +kernel

private theorem check072_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 8*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 8 j%5 := by decide +kernel

private theorem check072_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 9*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 9 j%5 := by decide +kernel

private theorem check072_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 10*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 10 j%5 := by decide +kernel

private theorem check072_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 11*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 11 j%5 := by decide +kernel

private theorem check072_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 12*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 12 j%5 := by decide +kernel

private theorem check072_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 13*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 13 j%5 := by decide +kernel

theorem checks072 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode i*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check072_00 j
  · exact check072_01 j
  · exact check072_02 j
  · exact check072_03 j
  · exact check072_04 j
  · exact check072_05 j
  · exact check072_06 j
  · exact check072_07 j
  · exact check072_08 j
  · exact check072_09 j
  · exact check072_10 j
  · exact check072_11 j
  · exact check072_12 j
  · exact check072_13 j

theorem matrix_node072 : (node072 A B)=CFSGJankoTwoSelectedCaches00.C003_data.matrix 5 := by
  change (node071 A B)*(node001 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedBaseCaches.B_data CFSGJankoTwoSelectedCaches00.C003_data
    CFSGJankoTwoSelectedProducts08.matrix_node071 CFSGJankoTwoSelectedBaseCaches.B_source_binding (by decide : 14*(5-1)^2 < 256) checks072

private theorem check073_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C073_digit 0 j%5 := by decide +kernel

private theorem check073_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C073_digit 1 j%5 := by decide +kernel

private theorem check073_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C073_digit 2 j%5 := by decide +kernel

private theorem check073_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C073_digit 3 j%5 := by decide +kernel

private theorem check073_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C073_digit 4 j%5 := by decide +kernel

private theorem check073_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C073_digit 5 j%5 := by decide +kernel

private theorem check073_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C073_digit 6 j%5 := by decide +kernel

private theorem check073_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C073_digit 7 j%5 := by decide +kernel

private theorem check073_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C073_digit 8 j%5 := by decide +kernel

private theorem check073_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C073_digit 9 j%5 := by decide +kernel

private theorem check073_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C073_digit 10 j%5 := by decide +kernel

private theorem check073_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C073_digit 11 j%5 := by decide +kernel

private theorem check073_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C073_digit 12 j%5 := by decide +kernel

private theorem check073_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C073_digit 13 j%5 := by decide +kernel

theorem checks073 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C073_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check073_00 j
  · exact check073_01 j
  · exact check073_02 j
  · exact check073_03 j
  · exact check073_04 j
  · exact check073_05 j
  · exact check073_06 j
  · exact check073_07 j
  · exact check073_08 j
  · exact check073_09 j
  · exact check073_10 j
  · exact check073_11 j
  · exact check073_12 j
  · exact check073_13 j

theorem matrix_node073 : (node073 A B)=CFSGJankoTwoSelectedCaches07.C073_data.matrix 5 := by
  change (node072 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches00.C003_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches07.C073_data
    CFSGJankoTwoSelectedProducts08.matrix_node072 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks073

private theorem check074_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C073_rowCode 0*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 0 j%5 := by decide +kernel

private theorem check074_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C073_rowCode 1*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 1 j%5 := by decide +kernel

private theorem check074_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C073_rowCode 2*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 2 j%5 := by decide +kernel

private theorem check074_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C073_rowCode 3*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 3 j%5 := by decide +kernel

private theorem check074_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C073_rowCode 4*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 4 j%5 := by decide +kernel

private theorem check074_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C073_rowCode 5*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 5 j%5 := by decide +kernel

private theorem check074_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C073_rowCode 6*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 6 j%5 := by decide +kernel

private theorem check074_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C073_rowCode 7*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 7 j%5 := by decide +kernel

private theorem check074_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C073_rowCode 8*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 8 j%5 := by decide +kernel

private theorem check074_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C073_rowCode 9*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 9 j%5 := by decide +kernel

private theorem check074_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C073_rowCode 10*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 10 j%5 := by decide +kernel

private theorem check074_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C073_rowCode 11*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 11 j%5 := by decide +kernel

private theorem check074_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C073_rowCode 12*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 12 j%5 := by decide +kernel

private theorem check074_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C073_rowCode 13*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 13 j%5 := by decide +kernel

theorem checks074 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C073_rowCode i*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check074_00 j
  · exact check074_01 j
  · exact check074_02 j
  · exact check074_03 j
  · exact check074_04 j
  · exact check074_05 j
  · exact check074_06 j
  · exact check074_07 j
  · exact check074_08 j
  · exact check074_09 j
  · exact check074_10 j
  · exact check074_11 j
  · exact check074_12 j
  · exact check074_13 j

theorem matrix_node074 : (node074 A B)=CFSGJankoTwoSelectedCaches06.C063_data.matrix 5 := by
  change (node073 A B)*(node001 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches07.C073_data CFSGJankoTwoSelectedBaseCaches.B_data CFSGJankoTwoSelectedCaches06.C063_data
    CFSGJankoTwoSelectedProducts08.matrix_node073 CFSGJankoTwoSelectedBaseCaches.B_source_binding (by decide : 14*(5-1)^2 < 256) checks074

private theorem check075_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C075_digit 0 j%5 := by decide +kernel

private theorem check075_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C075_digit 1 j%5 := by decide +kernel

private theorem check075_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C075_digit 2 j%5 := by decide +kernel

private theorem check075_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C075_digit 3 j%5 := by decide +kernel

private theorem check075_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C075_digit 4 j%5 := by decide +kernel

private theorem check075_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C075_digit 5 j%5 := by decide +kernel

private theorem check075_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C075_digit 6 j%5 := by decide +kernel

private theorem check075_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C075_digit 7 j%5 := by decide +kernel

private theorem check075_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C075_digit 8 j%5 := by decide +kernel

private theorem check075_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C075_digit 9 j%5 := by decide +kernel

private theorem check075_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C075_digit 10 j%5 := by decide +kernel

private theorem check075_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C075_digit 11 j%5 := by decide +kernel

private theorem check075_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C075_digit 12 j%5 := by decide +kernel

private theorem check075_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C075_digit 13 j%5 := by decide +kernel

theorem checks075 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C075_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check075_00 j
  · exact check075_01 j
  · exact check075_02 j
  · exact check075_03 j
  · exact check075_04 j
  · exact check075_05 j
  · exact check075_06 j
  · exact check075_07 j
  · exact check075_08 j
  · exact check075_09 j
  · exact check075_10 j
  · exact check075_11 j
  · exact check075_12 j
  · exact check075_13 j

theorem matrix_node075 : (node075 A B)=CFSGJankoTwoSelectedCaches07.C075_data.matrix 5 := by
  change (node074 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches06.C063_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches07.C075_data
    CFSGJankoTwoSelectedProducts08.matrix_node074 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks075

private theorem check076_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C075_rowCode 0*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C006_digit 0 j%5 := by decide +kernel

private theorem check076_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C075_rowCode 1*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C006_digit 1 j%5 := by decide +kernel

private theorem check076_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C075_rowCode 2*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C006_digit 2 j%5 := by decide +kernel

private theorem check076_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C075_rowCode 3*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C006_digit 3 j%5 := by decide +kernel

private theorem check076_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C075_rowCode 4*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C006_digit 4 j%5 := by decide +kernel

private theorem check076_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C075_rowCode 5*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C006_digit 5 j%5 := by decide +kernel

private theorem check076_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C075_rowCode 6*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C006_digit 6 j%5 := by decide +kernel

private theorem check076_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C075_rowCode 7*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C006_digit 7 j%5 := by decide +kernel

private theorem check076_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C075_rowCode 8*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C006_digit 8 j%5 := by decide +kernel

private theorem check076_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C075_rowCode 9*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C006_digit 9 j%5 := by decide +kernel

private theorem check076_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C075_rowCode 10*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C006_digit 10 j%5 := by decide +kernel

private theorem check076_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C075_rowCode 11*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C006_digit 11 j%5 := by decide +kernel

private theorem check076_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C075_rowCode 12*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C006_digit 12 j%5 := by decide +kernel

private theorem check076_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C075_rowCode 13*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C006_digit 13 j%5 := by decide +kernel

theorem checks076 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C075_rowCode i*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C006_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check076_00 j
  · exact check076_01 j
  · exact check076_02 j
  · exact check076_03 j
  · exact check076_04 j
  · exact check076_05 j
  · exact check076_06 j
  · exact check076_07 j
  · exact check076_08 j
  · exact check076_09 j
  · exact check076_10 j
  · exact check076_11 j
  · exact check076_12 j
  · exact check076_13 j

theorem matrix_node076 : (node076 A B)=CFSGJankoTwoSelectedCaches00.C006_data.matrix 5 := by
  change (node075 A B)*(node059 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches07.C075_data CFSGJankoTwoSelectedCaches06.C059_data CFSGJankoTwoSelectedCaches00.C006_data
    CFSGJankoTwoSelectedProducts08.matrix_node075 CFSGJankoTwoSelectedSeedPowerPilot.matrix_node059 (by decide : 14*(5-1)^2 < 256) checks076

private theorem check077_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C006_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C077_digit 0 j%5 := by decide +kernel

private theorem check077_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C006_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C077_digit 1 j%5 := by decide +kernel

private theorem check077_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C006_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C077_digit 2 j%5 := by decide +kernel

private theorem check077_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C006_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C077_digit 3 j%5 := by decide +kernel

private theorem check077_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C006_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C077_digit 4 j%5 := by decide +kernel

private theorem check077_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C006_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C077_digit 5 j%5 := by decide +kernel

private theorem check077_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C006_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C077_digit 6 j%5 := by decide +kernel

private theorem check077_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C006_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C077_digit 7 j%5 := by decide +kernel

private theorem check077_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C006_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C077_digit 8 j%5 := by decide +kernel

private theorem check077_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C006_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C077_digit 9 j%5 := by decide +kernel

private theorem check077_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C006_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C077_digit 10 j%5 := by decide +kernel

private theorem check077_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C006_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C077_digit 11 j%5 := by decide +kernel

private theorem check077_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C006_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C077_digit 12 j%5 := by decide +kernel

private theorem check077_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C006_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C077_digit 13 j%5 := by decide +kernel

theorem checks077 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C006_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C077_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check077_00 j
  · exact check077_01 j
  · exact check077_02 j
  · exact check077_03 j
  · exact check077_04 j
  · exact check077_05 j
  · exact check077_06 j
  · exact check077_07 j
  · exact check077_08 j
  · exact check077_09 j
  · exact check077_10 j
  · exact check077_11 j
  · exact check077_12 j
  · exact check077_13 j

theorem matrix_node077 : (node077 A B)=CFSGJankoTwoSelectedCaches08.C077_data.matrix 5 := by
  change (node076 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches00.C006_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches08.C077_data
    CFSGJankoTwoSelectedProducts08.matrix_node076 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks077

private theorem check078_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C077_rowCode 0*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C078_digit 0 j%5 := by decide +kernel

private theorem check078_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C077_rowCode 1*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C078_digit 1 j%5 := by decide +kernel

private theorem check078_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C077_rowCode 2*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C078_digit 2 j%5 := by decide +kernel

private theorem check078_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C077_rowCode 3*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C078_digit 3 j%5 := by decide +kernel

private theorem check078_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C077_rowCode 4*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C078_digit 4 j%5 := by decide +kernel

private theorem check078_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C077_rowCode 5*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C078_digit 5 j%5 := by decide +kernel

private theorem check078_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C077_rowCode 6*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C078_digit 6 j%5 := by decide +kernel

private theorem check078_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C077_rowCode 7*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C078_digit 7 j%5 := by decide +kernel

private theorem check078_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C077_rowCode 8*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C078_digit 8 j%5 := by decide +kernel

private theorem check078_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C077_rowCode 9*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C078_digit 9 j%5 := by decide +kernel

private theorem check078_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C077_rowCode 10*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C078_digit 10 j%5 := by decide +kernel

private theorem check078_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C077_rowCode 11*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C078_digit 11 j%5 := by decide +kernel

private theorem check078_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C077_rowCode 12*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C078_digit 12 j%5 := by decide +kernel

private theorem check078_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C077_rowCode 13*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C078_digit 13 j%5 := by decide +kernel

theorem checks078 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches08.C077_rowCode i*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches08.C078_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check078_00 j
  · exact check078_01 j
  · exact check078_02 j
  · exact check078_03 j
  · exact check078_04 j
  · exact check078_05 j
  · exact check078_06 j
  · exact check078_07 j
  · exact check078_08 j
  · exact check078_09 j
  · exact check078_10 j
  · exact check078_11 j
  · exact check078_12 j
  · exact check078_13 j

theorem matrix_node078 : (node078 A B)=CFSGJankoTwoSelectedCaches08.C078_data.matrix 5 := by
  change (node077 A B)*(node001 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches08.C077_data CFSGJankoTwoSelectedBaseCaches.B_data CFSGJankoTwoSelectedCaches08.C078_data
    CFSGJankoTwoSelectedProducts08.matrix_node077 CFSGJankoTwoSelectedBaseCaches.B_source_binding (by decide : 14*(5-1)^2 < 256) checks078

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts08
