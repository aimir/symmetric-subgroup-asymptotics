import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedPositiveWords
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches06
import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches00
import Mathlib.Tactic.FinCases

/-! Selected14/F5 whole products, one bounded14-column check per row. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedSeedPowerPilot
open MatrixKroneckerProductReflection
open CFSGJankoTwoSelectedPositiveWords
private abbrev A := CFSGJankoTwoSelectedBaseCaches.matrixA
private abbrev B := CFSGJankoTwoSelectedBaseCaches.matrixB

private theorem check058_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 0*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 0 j%5 := by decide +kernel

private theorem check058_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 1*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 1 j%5 := by decide +kernel

private theorem check058_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 2*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 2 j%5 := by decide +kernel

private theorem check058_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 3*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 3 j%5 := by decide +kernel

private theorem check058_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 4*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 4 j%5 := by decide +kernel

private theorem check058_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 5*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 5 j%5 := by decide +kernel

private theorem check058_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 6*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 6 j%5 := by decide +kernel

private theorem check058_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 7*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 7 j%5 := by decide +kernel

private theorem check058_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 8*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 8 j%5 := by decide +kernel

private theorem check058_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 9*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 9 j%5 := by decide +kernel

private theorem check058_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 10*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 10 j%5 := by decide +kernel

private theorem check058_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 11*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 11 j%5 := by decide +kernel

private theorem check058_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 12*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 12 j%5 := by decide +kernel

private theorem check058_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 13*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 13 j%5 := by decide +kernel

theorem checks058 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode i*CFSGJankoTwoSelectedBaseCaches.A_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check058_00 j
  · exact check058_01 j
  · exact check058_02 j
  · exact check058_03 j
  · exact check058_04 j
  · exact check058_05 j
  · exact check058_06 j
  · exact check058_07 j
  · exact check058_08 j
  · exact check058_09 j
  · exact check058_10 j
  · exact check058_11 j
  · exact check058_12 j
  · exact check058_13 j

theorem matrix_node058 : (node058 A B)=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 := by
  change (node000 A B)*(node000 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedBaseCaches.I_data
    CFSGJankoTwoSelectedBaseCaches.A_source_binding CFSGJankoTwoSelectedBaseCaches.A_source_binding (by decide : 14*(5-1)^2 < 256) checks058

private theorem check059_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 0*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C059_digit 0 j%5 := by decide +kernel

private theorem check059_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 1*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C059_digit 1 j%5 := by decide +kernel

private theorem check059_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 2*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C059_digit 2 j%5 := by decide +kernel

private theorem check059_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 3*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C059_digit 3 j%5 := by decide +kernel

private theorem check059_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 4*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C059_digit 4 j%5 := by decide +kernel

private theorem check059_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 5*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C059_digit 5 j%5 := by decide +kernel

private theorem check059_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 6*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C059_digit 6 j%5 := by decide +kernel

private theorem check059_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 7*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C059_digit 7 j%5 := by decide +kernel

private theorem check059_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 8*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C059_digit 8 j%5 := by decide +kernel

private theorem check059_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 9*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C059_digit 9 j%5 := by decide +kernel

private theorem check059_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 10*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C059_digit 10 j%5 := by decide +kernel

private theorem check059_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 11*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C059_digit 11 j%5 := by decide +kernel

private theorem check059_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 12*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C059_digit 12 j%5 := by decide +kernel

private theorem check059_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode 13*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C059_digit 13 j%5 := by decide +kernel

theorem checks059 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.B_rowCode i*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches06.C059_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check059_00 j
  · exact check059_01 j
  · exact check059_02 j
  · exact check059_03 j
  · exact check059_04 j
  · exact check059_05 j
  · exact check059_06 j
  · exact check059_07 j
  · exact check059_08 j
  · exact check059_09 j
  · exact check059_10 j
  · exact check059_11 j
  · exact check059_12 j
  · exact check059_13 j

theorem matrix_node059 : (node059 A B)=CFSGJankoTwoSelectedCaches06.C059_data.matrix 5 := by
  change (node001 A B)*(node001 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedBaseCaches.B_data CFSGJankoTwoSelectedBaseCaches.B_data CFSGJankoTwoSelectedCaches06.C059_data
    CFSGJankoTwoSelectedBaseCaches.B_source_binding CFSGJankoTwoSelectedBaseCaches.B_source_binding (by decide : 14*(5-1)^2 < 256) checks059

private theorem check060_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C059_rowCode 0*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 0 j%5 := by decide +kernel

private theorem check060_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C059_rowCode 1*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 1 j%5 := by decide +kernel

private theorem check060_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C059_rowCode 2*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 2 j%5 := by decide +kernel

private theorem check060_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C059_rowCode 3*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 3 j%5 := by decide +kernel

private theorem check060_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C059_rowCode 4*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 4 j%5 := by decide +kernel

private theorem check060_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C059_rowCode 5*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 5 j%5 := by decide +kernel

private theorem check060_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C059_rowCode 6*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 6 j%5 := by decide +kernel

private theorem check060_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C059_rowCode 7*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 7 j%5 := by decide +kernel

private theorem check060_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C059_rowCode 8*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 8 j%5 := by decide +kernel

private theorem check060_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C059_rowCode 9*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 9 j%5 := by decide +kernel

private theorem check060_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C059_rowCode 10*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 10 j%5 := by decide +kernel

private theorem check060_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C059_rowCode 11*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 11 j%5 := by decide +kernel

private theorem check060_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C059_rowCode 12*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 12 j%5 := by decide +kernel

private theorem check060_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C059_rowCode 13*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit 13 j%5 := by decide +kernel

theorem checks060 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedCaches06.C059_rowCode i*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedBaseCaches.I_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check060_00 j
  · exact check060_01 j
  · exact check060_02 j
  · exact check060_03 j
  · exact check060_04 j
  · exact check060_05 j
  · exact check060_06 j
  · exact check060_07 j
  · exact check060_08 j
  · exact check060_09 j
  · exact check060_10 j
  · exact check060_11 j
  · exact check060_12 j
  · exact check060_13 j

theorem matrix_node060 : (node060 A B)=CFSGJankoTwoSelectedBaseCaches.I_data.matrix 5 := by
  change (node059 A B)*(node001 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedCaches06.C059_data CFSGJankoTwoSelectedBaseCaches.B_data CFSGJankoTwoSelectedBaseCaches.I_data
    CFSGJankoTwoSelectedSeedPowerPilot.matrix_node059 CFSGJankoTwoSelectedBaseCaches.B_source_binding (by decide : 14*(5-1)^2 < 256) checks060

private theorem check061_00 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 0*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 0 j%5 := by decide +kernel

private theorem check061_01 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 1*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 1 j%5 := by decide +kernel

private theorem check061_02 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 2*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 2 j%5 := by decide +kernel

private theorem check061_03 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 3*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 3 j%5 := by decide +kernel

private theorem check061_04 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 4*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 4 j%5 := by decide +kernel

private theorem check061_05 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 5*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 5 j%5 := by decide +kernel

private theorem check061_06 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 6*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 6 j%5 := by decide +kernel

private theorem check061_07 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 7*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 7 j%5 := by decide +kernel

private theorem check061_08 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 8*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 8 j%5 := by decide +kernel

private theorem check061_09 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 9*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 9 j%5 := by decide +kernel

private theorem check061_10 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 10*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 10 j%5 := by decide +kernel

private theorem check061_11 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 11*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 11 j%5 := by decide +kernel

private theorem check061_12 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 12*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 12 j%5 := by decide +kernel

private theorem check061_13 : ∀ j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode 13*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit 13 j%5 := by decide +kernel

theorem checks061 : ∀ i j : Fin 14, (((CFSGJankoTwoSelectedBaseCaches.A_rowCode i*CFSGJankoTwoSelectedBaseCaches.B_columnCode j)/256^13)%256)%5=CFSGJankoTwoSelectedCaches00.C003_digit i j%5 := by
  intro i j
  fin_cases i
  · exact check061_00 j
  · exact check061_01 j
  · exact check061_02 j
  · exact check061_03 j
  · exact check061_04 j
  · exact check061_05 j
  · exact check061_06 j
  · exact check061_07 j
  · exact check061_08 j
  · exact check061_09 j
  · exact check061_10 j
  · exact check061_11 j
  · exact check061_12 j
  · exact check061_13 j

theorem matrix_node061 : (node061 A B)=CFSGJankoTwoSelectedCaches00.C003_data.matrix 5 := by
  change (node000 A B)*(node001 A B)=_
  exact product_eq_of_data (by decide : 0 < 14) _ _
    CFSGJankoTwoSelectedBaseCaches.A_data CFSGJankoTwoSelectedBaseCaches.B_data CFSGJankoTwoSelectedCaches00.C003_data
    CFSGJankoTwoSelectedBaseCaches.A_source_binding CFSGJankoTwoSelectedBaseCaches.B_source_binding (by decide : 14*(5-1)^2 < 256) checks061

theorem wholeA_square : A^2=1 := by
  simpa only [pow_two,node058,node000] using (matrix_node058.trans CFSGJankoTwoSelectedBaseCaches.identity_binding)

theorem wholeB_cube : B^3=1 := by
  calc
    B^3=B^2*B := pow_succ B 2
    _=1 := by
      simpa only [pow_two,node060,node059,node001] using
        (matrix_node060.trans CFSGJankoTwoSelectedBaseCaches.identity_binding)

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedSeedPowerPilot
