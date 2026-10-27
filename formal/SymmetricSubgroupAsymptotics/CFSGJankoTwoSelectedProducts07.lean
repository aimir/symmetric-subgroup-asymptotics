import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedPositiveWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches00
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches06
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedSeedPowerPilot
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches07
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts06
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts07
open MatrixKroneckerProductReflection
open CFSGJankoTwoSelectedPositiveWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check063_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 0*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 0 j%5 := by decide +kernel

private theorem check063_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 1*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 1 j%5 := by decide +kernel

private theorem check063_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 2*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 2 j%5 := by decide +kernel

private theorem check063_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 3*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 3 j%5 := by decide +kernel

private theorem check063_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 4*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 4 j%5 := by decide +kernel

private theorem check063_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 5*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 5 j%5 := by decide +kernel

private theorem check063_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 6*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 6 j%5 := by decide +kernel

private theorem check063_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 7*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 7 j%5 := by decide +kernel

private theorem check063_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 8*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 8 j%5 := by decide +kernel

private theorem check063_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 9*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 9 j%5 := by decide +kernel

private theorem check063_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 10*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 10 j%5 := by decide +kernel

private theorem check063_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 11*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 11 j%5 := by decide +kernel

private theorem check063_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 12*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 12 j%5 := by decide +kernel

private theorem check063_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 13*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit 13 j%5 := by decide +kernel

theorem checks063 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode i*CFSGJankoTwoSelectedCaches00.C003_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C063_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check063_00 j
  · exact check063_01 j
  · exact check063_02 j
  · exact check063_03 j
  · exact check063_04 j
  · exact check063_05 j
  · exact check063_06 j
  · exact check063_07 j
  · exact check063_08 j
  · exact check063_09 j
  · exact check063_10 j
  · exact check063_11 j
  · exact check063_12 j
  · exact check063_13 j

theorem matrix_node063 : (node063 A B)=CFSGJankoTwoSelectedCaches06.C063_data.matrix 5 := by
  change (node061 A B)*(node061 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches00.C003_data CFSGJankoTwoSelectedCaches00.C003_data CFSGJankoTwoSelectedCaches06.C063_data
    CFSGJankoTwoSelectedSeedPowerPilot.matrix_node061 CFSGJankoTwoSelectedSeedPowerPilot.matrix_node061 (by decide : 14*(5-1)^2 < 256) checks063

private theorem check064_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 0*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C064_digit 0 j%5 := by decide +kernel

private theorem check064_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 1*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C064_digit 1 j%5 := by decide +kernel

private theorem check064_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 2*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C064_digit 2 j%5 := by decide +kernel

private theorem check064_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 3*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C064_digit 3 j%5 := by decide +kernel

private theorem check064_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 4*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C064_digit 4 j%5 := by decide +kernel

private theorem check064_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 5*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C064_digit 5 j%5 := by decide +kernel

private theorem check064_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 6*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C064_digit 6 j%5 := by decide +kernel

private theorem check064_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 7*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C064_digit 7 j%5 := by decide +kernel

private theorem check064_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 8*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C064_digit 8 j%5 := by decide +kernel

private theorem check064_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 9*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C064_digit 9 j%5 := by decide +kernel

private theorem check064_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 10*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C064_digit 10 j%5 := by decide +kernel

private theorem check064_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 11*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C064_digit 11 j%5 := by decide +kernel

private theorem check064_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 12*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C064_digit 12 j%5 := by decide +kernel

private theorem check064_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode 13*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C064_digit 13 j%5 := by decide +kernel

theorem checks064 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C003_rowCode i*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C064_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check064_00 j
  · exact check064_01 j
  · exact check064_02 j
  · exact check064_03 j
  · exact check064_04 j
  · exact check064_05 j
  · exact check064_06 j
  · exact check064_07 j
  · exact check064_08 j
  · exact check064_09 j
  · exact check064_10 j
  · exact check064_11 j
  · exact check064_12 j
  · exact check064_13 j

theorem matrix_node064 : (node064 A B)=CFSGJankoTwoSelectedCaches07.C064_data.matrix 5 := by
  change (node062 A B)*(node063 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches00.C003_data CFSGJankoTwoSelectedCaches06.C063_data CFSGJankoTwoSelectedCaches07.C064_data
    CFSGJankoTwoSelectedProducts06.matrix_node062 CFSGJankoTwoSelectedProducts07.matrix_node063 (by decide : 14*(5-1)^2 < 256) checks064

private theorem check065_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 0*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C065_digit 0 j%5 := by decide +kernel

private theorem check065_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 1*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C065_digit 1 j%5 := by decide +kernel

private theorem check065_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 2*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C065_digit 2 j%5 := by decide +kernel

private theorem check065_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 3*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C065_digit 3 j%5 := by decide +kernel

private theorem check065_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 4*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C065_digit 4 j%5 := by decide +kernel

private theorem check065_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 5*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C065_digit 5 j%5 := by decide +kernel

private theorem check065_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 6*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C065_digit 6 j%5 := by decide +kernel

private theorem check065_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 7*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C065_digit 7 j%5 := by decide +kernel

private theorem check065_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 8*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C065_digit 8 j%5 := by decide +kernel

private theorem check065_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 9*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C065_digit 9 j%5 := by decide +kernel

private theorem check065_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 10*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C065_digit 10 j%5 := by decide +kernel

private theorem check065_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 11*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C065_digit 11 j%5 := by decide +kernel

private theorem check065_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 12*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C065_digit 12 j%5 := by decide +kernel

private theorem check065_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode 13*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C065_digit 13 j%5 := by decide +kernel

theorem checks065 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C063_rowCode i*CFSGJankoTwoSelectedCaches06.C063_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C065_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check065_00 j
  · exact check065_01 j
  · exact check065_02 j
  · exact check065_03 j
  · exact check065_04 j
  · exact check065_05 j
  · exact check065_06 j
  · exact check065_07 j
  · exact check065_08 j
  · exact check065_09 j
  · exact check065_10 j
  · exact check065_11 j
  · exact check065_12 j
  · exact check065_13 j

theorem matrix_node065 : (node065 A B)=CFSGJankoTwoSelectedCaches07.C065_data.matrix 5 := by
  change (node063 A B)*(node063 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches06.C063_data CFSGJankoTwoSelectedCaches06.C063_data CFSGJankoTwoSelectedCaches07.C065_data
    CFSGJankoTwoSelectedProducts07.matrix_node063 CFSGJankoTwoSelectedProducts07.matrix_node063 (by decide : 14*(5-1)^2 < 256) checks065

private theorem check066_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C064_rowCode 0*CFSGJankoTwoSelectedCaches07.C065_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 0 j%5 := by decide +kernel

private theorem check066_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C064_rowCode 1*CFSGJankoTwoSelectedCaches07.C065_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 1 j%5 := by decide +kernel

private theorem check066_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C064_rowCode 2*CFSGJankoTwoSelectedCaches07.C065_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 2 j%5 := by decide +kernel

private theorem check066_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C064_rowCode 3*CFSGJankoTwoSelectedCaches07.C065_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 3 j%5 := by decide +kernel

private theorem check066_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C064_rowCode 4*CFSGJankoTwoSelectedCaches07.C065_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 4 j%5 := by decide +kernel

private theorem check066_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C064_rowCode 5*CFSGJankoTwoSelectedCaches07.C065_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 5 j%5 := by decide +kernel

private theorem check066_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C064_rowCode 6*CFSGJankoTwoSelectedCaches07.C065_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 6 j%5 := by decide +kernel

private theorem check066_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C064_rowCode 7*CFSGJankoTwoSelectedCaches07.C065_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 7 j%5 := by decide +kernel

private theorem check066_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C064_rowCode 8*CFSGJankoTwoSelectedCaches07.C065_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 8 j%5 := by decide +kernel

private theorem check066_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C064_rowCode 9*CFSGJankoTwoSelectedCaches07.C065_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 9 j%5 := by decide +kernel

private theorem check066_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C064_rowCode 10*CFSGJankoTwoSelectedCaches07.C065_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 10 j%5 := by decide +kernel

private theorem check066_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C064_rowCode 11*CFSGJankoTwoSelectedCaches07.C065_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 11 j%5 := by decide +kernel

private theorem check066_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C064_rowCode 12*CFSGJankoTwoSelectedCaches07.C065_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 12 j%5 := by decide +kernel

private theorem check066_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C064_rowCode 13*CFSGJankoTwoSelectedCaches07.C065_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 13 j%5 := by decide +kernel

theorem checks066 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C064_rowCode i*CFSGJankoTwoSelectedCaches07.C065_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check066_00 j
  · exact check066_01 j
  · exact check066_02 j
  · exact check066_03 j
  · exact check066_04 j
  · exact check066_05 j
  · exact check066_06 j
  · exact check066_07 j
  · exact check066_08 j
  · exact check066_09 j
  · exact check066_10 j
  · exact check066_11 j
  · exact check066_12 j
  · exact check066_13 j

theorem matrix_node066 : (node066 A B)=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 := by
  change (node064 A B)*(node065 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches07.C064_data CFSGJankoTwoSelectedCaches07.C065_data CFSGJankoTwoSelectedBaseCaches.I_data
    CFSGJankoTwoSelectedProducts07.matrix_node064 CFSGJankoTwoSelectedProducts07.matrix_node065 (by decide : 14*(5-1)^2 < 256) checks066

private theorem check067_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 0 j%5 := by decide +kernel

private theorem check067_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 1 j%5 := by decide +kernel

private theorem check067_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 2 j%5 := by decide +kernel

private theorem check067_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 3 j%5 := by decide +kernel

private theorem check067_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 4 j%5 := by decide +kernel

private theorem check067_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 5 j%5 := by decide +kernel

private theorem check067_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 6 j%5 := by decide +kernel

private theorem check067_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 7 j%5 := by decide +kernel

private theorem check067_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 8 j%5 := by decide +kernel

private theorem check067_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 9 j%5 := by decide +kernel

private theorem check067_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 10 j%5 := by decide +kernel

private theorem check067_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 11 j%5 := by decide +kernel

private theorem check067_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 12 j%5 := by decide +kernel

private theorem check067_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit 13 j%5 := by decide +kernel

theorem checks067 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.I_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.A_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check067_00 j
  · exact check067_01 j
  · exact check067_02 j
  · exact check067_03 j
  · exact check067_04 j
  · exact check067_05 j
  · exact check067_06 j
  · exact check067_07 j
  · exact check067_08 j
  · exact check067_09 j
  · exact check067_10 j
  · exact check067_11 j
  · exact check067_12 j
  · exact check067_13 j

theorem matrix_node067 : (node067 A B)=CFSGJankoTwoSelectedBaseCaches.A_data.matrix 5 := by
  change (node002 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedBaseCaches.I_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedBaseCaches.A_data
    (show (1 : Matrix (Fin 14) (Fin 14) (ZMod 5))=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 from CFSGJankoTwoSelectedBaseCaches.identity_binding.symm) CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks067

private theorem check068_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 0*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C004_digit 0 j%5 := by decide +kernel

private theorem check068_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 1*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C004_digit 1 j%5 := by decide +kernel

private theorem check068_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 2*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C004_digit 2 j%5 := by decide +kernel

private theorem check068_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 3*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C004_digit 3 j%5 := by decide +kernel

private theorem check068_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 4*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C004_digit 4 j%5 := by decide +kernel

private theorem check068_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 5*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C004_digit 5 j%5 := by decide +kernel

private theorem check068_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 6*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C004_digit 6 j%5 := by decide +kernel

private theorem check068_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 7*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C004_digit 7 j%5 := by decide +kernel

private theorem check068_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 8*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C004_digit 8 j%5 := by decide +kernel

private theorem check068_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 9*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C004_digit 9 j%5 := by decide +kernel

private theorem check068_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 10*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C004_digit 10 j%5 := by decide +kernel

private theorem check068_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 11*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C004_digit 11 j%5 := by decide +kernel

private theorem check068_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 12*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C004_digit 12 j%5 := by decide +kernel

private theorem check068_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 13*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C004_digit 13 j%5 := by decide +kernel

theorem checks068 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode i*CFSGJankoTwoSelectedCaches06.C059_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C004_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check068_00 j
  · exact check068_01 j
  · exact check068_02 j
  · exact check068_03 j
  · exact check068_04 j
  · exact check068_05 j
  · exact check068_06 j
  · exact check068_07 j
  · exact check068_08 j
  · exact check068_09 j
  · exact check068_10 j
  · exact check068_11 j
  · exact check068_12 j
  · exact check068_13 j

theorem matrix_node068 : (node068 A B)=CFSGJankoTwoSelectedCaches00.C004_data.matrix 5 := by
  change (node067 A B)*(node059 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches06.C059_data CFSGJankoTwoSelectedCaches00.C004_data
    CFSGJankoTwoSelectedProducts07.matrix_node067 CFSGJankoTwoSelectedSeedPowerPilot.matrix_node059 (by decide : 14*(5-1)^2 < 256) checks068

private theorem check069_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C004_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C069_digit 0 j%5 := by decide +kernel

private theorem check069_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C004_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C069_digit 1 j%5 := by decide +kernel

private theorem check069_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C004_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C069_digit 2 j%5 := by decide +kernel

private theorem check069_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C004_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C069_digit 3 j%5 := by decide +kernel

private theorem check069_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C004_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C069_digit 4 j%5 := by decide +kernel

private theorem check069_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C004_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C069_digit 5 j%5 := by decide +kernel

private theorem check069_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C004_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C069_digit 6 j%5 := by decide +kernel

private theorem check069_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C004_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C069_digit 7 j%5 := by decide +kernel

private theorem check069_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C004_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C069_digit 8 j%5 := by decide +kernel

private theorem check069_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C004_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C069_digit 9 j%5 := by decide +kernel

private theorem check069_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C004_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C069_digit 10 j%5 := by decide +kernel

private theorem check069_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C004_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C069_digit 11 j%5 := by decide +kernel

private theorem check069_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C004_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C069_digit 12 j%5 := by decide +kernel

private theorem check069_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C004_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C069_digit 13 j%5 := by decide +kernel

theorem checks069 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches00.C004_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C069_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check069_00 j
  · exact check069_01 j
  · exact check069_02 j
  · exact check069_03 j
  · exact check069_04 j
  · exact check069_05 j
  · exact check069_06 j
  · exact check069_07 j
  · exact check069_08 j
  · exact check069_09 j
  · exact check069_10 j
  · exact check069_11 j
  · exact check069_12 j
  · exact check069_13 j

theorem matrix_node069 : (node069 A B)=CFSGJankoTwoSelectedCaches07.C069_data.matrix 5 := by
  change (node068 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches00.C004_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedCaches07.C069_data
    CFSGJankoTwoSelectedProducts07.matrix_node068 CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks069

private theorem check070_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C069_rowCode 0*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C070_digit 0 j%5 := by decide +kernel

private theorem check070_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C069_rowCode 1*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C070_digit 1 j%5 := by decide +kernel

private theorem check070_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C069_rowCode 2*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C070_digit 2 j%5 := by decide +kernel

private theorem check070_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C069_rowCode 3*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C070_digit 3 j%5 := by decide +kernel

private theorem check070_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C069_rowCode 4*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C070_digit 4 j%5 := by decide +kernel

private theorem check070_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C069_rowCode 5*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C070_digit 5 j%5 := by decide +kernel

private theorem check070_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C069_rowCode 6*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C070_digit 6 j%5 := by decide +kernel

private theorem check070_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C069_rowCode 7*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C070_digit 7 j%5 := by decide +kernel

private theorem check070_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C069_rowCode 8*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C070_digit 8 j%5 := by decide +kernel

private theorem check070_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C069_rowCode 9*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C070_digit 9 j%5 := by decide +kernel

private theorem check070_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C069_rowCode 10*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C070_digit 10 j%5 := by decide +kernel

private theorem check070_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C069_rowCode 11*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C070_digit 11 j%5 := by decide +kernel

private theorem check070_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C069_rowCode 12*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C070_digit 12 j%5 := by decide +kernel

private theorem check070_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C069_rowCode 13*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C070_digit 13 j%5 := by decide +kernel

theorem checks070 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches07.C069_rowCode i*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches07.C070_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check070_00 j
  · exact check070_01 j
  · exact check070_02 j
  · exact check070_03 j
  · exact check070_04 j
  · exact check070_05 j
  · exact check070_06 j
  · exact check070_07 j
  · exact check070_08 j
  · exact check070_09 j
  · exact check070_10 j
  · exact check070_11 j
  · exact check070_12 j
  · exact check070_13 j

theorem matrix_node070 : (node070 A B)=CFSGJankoTwoSelectedCaches07.C070_data.matrix 5 := by
  change (node069 A B)*(node001 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches07.C069_data CFSGJankoTwoSelectedBaseCaches.B_data CFSGJankoTwoSelectedCaches07.C070_data
    CFSGJankoTwoSelectedProducts07.matrix_node069 CFSGJankoTwoSelectedBaseCaches.B_source_binding (by decide : 14*(5-1)^2 < 256) checks070

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedProducts07
