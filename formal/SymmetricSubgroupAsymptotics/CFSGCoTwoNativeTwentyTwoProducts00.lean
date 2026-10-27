import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoBaseCaches
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches00
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches01
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoPowerPilot
import Mathlib.Tactic.FinCases

/-! Fixed Co2 positive products; every whole matrix entry checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts00
open MatrixKroneckerProductReflection

private theorem check_B3_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 0 j%2 := by decide +kernel

private theorem check_B3_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 1 j%2 := by decide +kernel

private theorem check_B3_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 2 j%2 := by decide +kernel

private theorem check_B3_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 3 j%2 := by decide +kernel

private theorem check_B3_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 4 j%2 := by decide +kernel

private theorem check_B3_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 5 j%2 := by decide +kernel

private theorem check_B3_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 6 j%2 := by decide +kernel

private theorem check_B3_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 7 j%2 := by decide +kernel

private theorem check_B3_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 8 j%2 := by decide +kernel

private theorem check_B3_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 9 j%2 := by decide +kernel

private theorem check_B3_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 10 j%2 := by decide +kernel

private theorem check_B3_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 11 j%2 := by decide +kernel

private theorem check_B3_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 12 j%2 := by decide +kernel

private theorem check_B3_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 13 j%2 := by decide +kernel

private theorem check_B3_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 14 j%2 := by decide +kernel

private theorem check_B3_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 15 j%2 := by decide +kernel

private theorem check_B3_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 16 j%2 := by decide +kernel

private theorem check_B3_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 17 j%2 := by decide +kernel

private theorem check_B3_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 18 j%2 := by decide +kernel

private theorem check_B3_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 19 j%2 := by decide +kernel

private theorem check_B3_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 20 j%2 := by decide +kernel

private theorem check_B3_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit 21 j%2 := by decide +kernel

theorem checks_B3 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.B3_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_B3_00 j
  · exact check_B3_01 j
  · exact check_B3_02 j
  · exact check_B3_03 j
  · exact check_B3_04 j
  · exact check_B3_05 j
  · exact check_B3_06 j
  · exact check_B3_07 j
  · exact check_B3_08 j
  · exact check_B3_09 j
  · exact check_B3_10 j
  · exact check_B3_11 j
  · exact check_B3_12 j
  · exact check_B3_13 j
  · exact check_B3_14 j
  · exact check_B3_15 j
  · exact check_B3_16 j
  · exact check_B3_17 j
  · exact check_B3_18 j
  · exact check_B3_19 j
  · exact check_B3_20 j
  · exact check_B3_21 j

def matrix_B3 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixB)

theorem cache_B3 : matrix_B3=CFSGCoTwoNativeTwentyTwoCaches00.B3_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoBaseCaches.B2_data CFSGCoTwoNativeTwentyTwoBaseCaches.B_data CFSGCoTwoNativeTwentyTwoCaches00.B3_data
    CFSGCoTwoNativeTwentyTwoPowerPilot.cache_B2 CFSGCoTwoNativeTwentyTwoBaseCaches.B_source_binding
    (by decide : 22*(2-1)^2<32) checks_B3

private theorem check_R03p01_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 0 j%2 := by decide +kernel

private theorem check_R03p01_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 1 j%2 := by decide +kernel

private theorem check_R03p01_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 2 j%2 := by decide +kernel

private theorem check_R03p01_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 3 j%2 := by decide +kernel

private theorem check_R03p01_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 4 j%2 := by decide +kernel

private theorem check_R03p01_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 5 j%2 := by decide +kernel

private theorem check_R03p01_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 6 j%2 := by decide +kernel

private theorem check_R03p01_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 7 j%2 := by decide +kernel

private theorem check_R03p01_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 8 j%2 := by decide +kernel

private theorem check_R03p01_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 9 j%2 := by decide +kernel

private theorem check_R03p01_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 10 j%2 := by decide +kernel

private theorem check_R03p01_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 11 j%2 := by decide +kernel

private theorem check_R03p01_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 12 j%2 := by decide +kernel

private theorem check_R03p01_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 13 j%2 := by decide +kernel

private theorem check_R03p01_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 14 j%2 := by decide +kernel

private theorem check_R03p01_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 15 j%2 := by decide +kernel

private theorem check_R03p01_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 16 j%2 := by decide +kernel

private theorem check_R03p01_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 17 j%2 := by decide +kernel

private theorem check_R03p01_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 18 j%2 := by decide +kernel

private theorem check_R03p01_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 19 j%2 := by decide +kernel

private theorem check_R03p01_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 20 j%2 := by decide +kernel

private theorem check_R03p01_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit 21 j%2 := by decide +kernel

theorem checks_R03p01 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R03p01_00 j
  · exact check_R03p01_01 j
  · exact check_R03p01_02 j
  · exact check_R03p01_03 j
  · exact check_R03p01_04 j
  · exact check_R03p01_05 j
  · exact check_R03p01_06 j
  · exact check_R03p01_07 j
  · exact check_R03p01_08 j
  · exact check_R03p01_09 j
  · exact check_R03p01_10 j
  · exact check_R03p01_11 j
  · exact check_R03p01_12 j
  · exact check_R03p01_13 j
  · exact check_R03p01_14 j
  · exact check_R03p01_15 j
  · exact check_R03p01_16 j
  · exact check_R03p01_17 j
  · exact check_R03p01_18 j
  · exact check_R03p01_19 j
  · exact check_R03p01_20 j
  · exact check_R03p01_21 j

def matrix_R03p01 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)

theorem cache_R03p01 : matrix_R03p01=CFSGCoTwoNativeTwentyTwoCaches00.R03p01_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoBaseCaches.B2_data CFSGCoTwoNativeTwentyTwoCaches00.R03p01_data
    CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding CFSGCoTwoNativeTwentyTwoPowerPilot.cache_B2
    (by decide : 22*(2-1)^2<32) checks_R03p01

private theorem check_R03e02_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 0 j%2 := by decide +kernel

private theorem check_R03e02_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 1 j%2 := by decide +kernel

private theorem check_R03e02_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 2 j%2 := by decide +kernel

private theorem check_R03e02_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 3 j%2 := by decide +kernel

private theorem check_R03e02_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 4 j%2 := by decide +kernel

private theorem check_R03e02_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 5 j%2 := by decide +kernel

private theorem check_R03e02_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 6 j%2 := by decide +kernel

private theorem check_R03e02_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 7 j%2 := by decide +kernel

private theorem check_R03e02_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 8 j%2 := by decide +kernel

private theorem check_R03e02_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 9 j%2 := by decide +kernel

private theorem check_R03e02_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 10 j%2 := by decide +kernel

private theorem check_R03e02_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 11 j%2 := by decide +kernel

private theorem check_R03e02_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 12 j%2 := by decide +kernel

private theorem check_R03e02_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 13 j%2 := by decide +kernel

private theorem check_R03e02_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 14 j%2 := by decide +kernel

private theorem check_R03e02_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 15 j%2 := by decide +kernel

private theorem check_R03e02_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 16 j%2 := by decide +kernel

private theorem check_R03e02_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 17 j%2 := by decide +kernel

private theorem check_R03e02_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 18 j%2 := by decide +kernel

private theorem check_R03e02_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 19 j%2 := by decide +kernel

private theorem check_R03e02_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 20 j%2 := by decide +kernel

private theorem check_R03e02_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit 21 j%2 := by decide +kernel

theorem checks_R03e02 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode i*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R03e02_00 j
  · exact check_R03e02_01 j
  · exact check_R03e02_02 j
  · exact check_R03e02_03 j
  · exact check_R03e02_04 j
  · exact check_R03e02_05 j
  · exact check_R03e02_06 j
  · exact check_R03e02_07 j
  · exact check_R03e02_08 j
  · exact check_R03e02_09 j
  · exact check_R03e02_10 j
  · exact check_R03e02_11 j
  · exact check_R03e02_12 j
  · exact check_R03e02_13 j
  · exact check_R03e02_14 j
  · exact check_R03e02_15 j
  · exact check_R03e02_16 j
  · exact check_R03e02_17 j
  · exact check_R03e02_18 j
  · exact check_R03e02_19 j
  · exact check_R03e02_20 j
  · exact check_R03e02_21 j

def matrix_R03e02 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03p01)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03p01)

theorem cache_R03e02 : matrix_R03e02=CFSGCoTwoNativeTwentyTwoCaches00.R03e02_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches00.R03p01_data CFSGCoTwoNativeTwentyTwoCaches00.R03p01_data CFSGCoTwoNativeTwentyTwoCaches00.R03e02_data
    CFSGCoTwoNativeTwentyTwoProducts00.cache_R03p01 CFSGCoTwoNativeTwentyTwoProducts00.cache_R03p01
    (by decide : 22*(2-1)^2<32) checks_R03e02

private theorem check_R03e04_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 0 j%2 := by decide +kernel

private theorem check_R03e04_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 1 j%2 := by decide +kernel

private theorem check_R03e04_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 2 j%2 := by decide +kernel

private theorem check_R03e04_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 3 j%2 := by decide +kernel

private theorem check_R03e04_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 4 j%2 := by decide +kernel

private theorem check_R03e04_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 5 j%2 := by decide +kernel

private theorem check_R03e04_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 6 j%2 := by decide +kernel

private theorem check_R03e04_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 7 j%2 := by decide +kernel

private theorem check_R03e04_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 8 j%2 := by decide +kernel

private theorem check_R03e04_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 9 j%2 := by decide +kernel

private theorem check_R03e04_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 10 j%2 := by decide +kernel

private theorem check_R03e04_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 11 j%2 := by decide +kernel

private theorem check_R03e04_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 12 j%2 := by decide +kernel

private theorem check_R03e04_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 13 j%2 := by decide +kernel

private theorem check_R03e04_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 14 j%2 := by decide +kernel

private theorem check_R03e04_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 15 j%2 := by decide +kernel

private theorem check_R03e04_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 16 j%2 := by decide +kernel

private theorem check_R03e04_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 17 j%2 := by decide +kernel

private theorem check_R03e04_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 18 j%2 := by decide +kernel

private theorem check_R03e04_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 19 j%2 := by decide +kernel

private theorem check_R03e04_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 20 j%2 := by decide +kernel

private theorem check_R03e04_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit 21 j%2 := by decide +kernel

theorem checks_R03e04 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e02_rowCode i*CFSGCoTwoNativeTwentyTwoCaches00.R03e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R03e04_00 j
  · exact check_R03e04_01 j
  · exact check_R03e04_02 j
  · exact check_R03e04_03 j
  · exact check_R03e04_04 j
  · exact check_R03e04_05 j
  · exact check_R03e04_06 j
  · exact check_R03e04_07 j
  · exact check_R03e04_08 j
  · exact check_R03e04_09 j
  · exact check_R03e04_10 j
  · exact check_R03e04_11 j
  · exact check_R03e04_12 j
  · exact check_R03e04_13 j
  · exact check_R03e04_14 j
  · exact check_R03e04_15 j
  · exact check_R03e04_16 j
  · exact check_R03e04_17 j
  · exact check_R03e04_18 j
  · exact check_R03e04_19 j
  · exact check_R03e04_20 j
  · exact check_R03e04_21 j

def matrix_R03e04 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03e02)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03e02)

theorem cache_R03e04 : matrix_R03e04=CFSGCoTwoNativeTwentyTwoCaches00.R03e04_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches00.R03e02_data CFSGCoTwoNativeTwentyTwoCaches00.R03e02_data CFSGCoTwoNativeTwentyTwoCaches00.R03e04_data
    CFSGCoTwoNativeTwentyTwoProducts00.cache_R03e02 CFSGCoTwoNativeTwentyTwoProducts00.cache_R03e02
    (by decide : 22*(2-1)^2<32) checks_R03e04

private theorem check_R03e08_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 0 j%2 := by decide +kernel

private theorem check_R03e08_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 1 j%2 := by decide +kernel

private theorem check_R03e08_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 2 j%2 := by decide +kernel

private theorem check_R03e08_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 3 j%2 := by decide +kernel

private theorem check_R03e08_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 4 j%2 := by decide +kernel

private theorem check_R03e08_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 5 j%2 := by decide +kernel

private theorem check_R03e08_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 6 j%2 := by decide +kernel

private theorem check_R03e08_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 7 j%2 := by decide +kernel

private theorem check_R03e08_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 8 j%2 := by decide +kernel

private theorem check_R03e08_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 9 j%2 := by decide +kernel

private theorem check_R03e08_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 10 j%2 := by decide +kernel

private theorem check_R03e08_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 11 j%2 := by decide +kernel

private theorem check_R03e08_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 12 j%2 := by decide +kernel

private theorem check_R03e08_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 13 j%2 := by decide +kernel

private theorem check_R03e08_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 14 j%2 := by decide +kernel

private theorem check_R03e08_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 15 j%2 := by decide +kernel

private theorem check_R03e08_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 16 j%2 := by decide +kernel

private theorem check_R03e08_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 17 j%2 := by decide +kernel

private theorem check_R03e08_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 18 j%2 := by decide +kernel

private theorem check_R03e08_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 19 j%2 := by decide +kernel

private theorem check_R03e08_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 20 j%2 := by decide +kernel

private theorem check_R03e08_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit 21 j%2 := by decide +kernel

theorem checks_R03e08 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03e04_rowCode i*CFSGCoTwoNativeTwentyTwoCaches00.R03e04_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R03e08_00 j
  · exact check_R03e08_01 j
  · exact check_R03e08_02 j
  · exact check_R03e08_03 j
  · exact check_R03e08_04 j
  · exact check_R03e08_05 j
  · exact check_R03e08_06 j
  · exact check_R03e08_07 j
  · exact check_R03e08_08 j
  · exact check_R03e08_09 j
  · exact check_R03e08_10 j
  · exact check_R03e08_11 j
  · exact check_R03e08_12 j
  · exact check_R03e08_13 j
  · exact check_R03e08_14 j
  · exact check_R03e08_15 j
  · exact check_R03e08_16 j
  · exact check_R03e08_17 j
  · exact check_R03e08_18 j
  · exact check_R03e08_19 j
  · exact check_R03e08_20 j
  · exact check_R03e08_21 j

def matrix_R03e08 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03e04)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03e04)

theorem cache_R03e08 : matrix_R03e08=CFSGCoTwoNativeTwentyTwoCaches01.R03e08_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches00.R03e04_data CFSGCoTwoNativeTwentyTwoCaches00.R03e04_data CFSGCoTwoNativeTwentyTwoCaches01.R03e08_data
    CFSGCoTwoNativeTwentyTwoProducts00.cache_R03e04 CFSGCoTwoNativeTwentyTwoProducts00.cache_R03e04
    (by decide : 22*(2-1)^2<32) checks_R03e08

private theorem check_R03e09_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 0 j%2 := by decide +kernel

private theorem check_R03e09_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 1 j%2 := by decide +kernel

private theorem check_R03e09_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 2 j%2 := by decide +kernel

private theorem check_R03e09_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 3 j%2 := by decide +kernel

private theorem check_R03e09_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 4 j%2 := by decide +kernel

private theorem check_R03e09_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 5 j%2 := by decide +kernel

private theorem check_R03e09_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 6 j%2 := by decide +kernel

private theorem check_R03e09_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 7 j%2 := by decide +kernel

private theorem check_R03e09_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 8 j%2 := by decide +kernel

private theorem check_R03e09_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 9 j%2 := by decide +kernel

private theorem check_R03e09_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 10 j%2 := by decide +kernel

private theorem check_R03e09_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 11 j%2 := by decide +kernel

private theorem check_R03e09_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 12 j%2 := by decide +kernel

private theorem check_R03e09_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 13 j%2 := by decide +kernel

private theorem check_R03e09_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 14 j%2 := by decide +kernel

private theorem check_R03e09_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 15 j%2 := by decide +kernel

private theorem check_R03e09_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 16 j%2 := by decide +kernel

private theorem check_R03e09_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 17 j%2 := by decide +kernel

private theorem check_R03e09_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 18 j%2 := by decide +kernel

private theorem check_R03e09_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 19 j%2 := by decide +kernel

private theorem check_R03e09_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 20 j%2 := by decide +kernel

private theorem check_R03e09_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 21 j%2 := by decide +kernel

theorem checks_R03e09 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R03e08_rowCode i*CFSGCoTwoNativeTwentyTwoCaches00.R03p01_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R03e09_00 j
  · exact check_R03e09_01 j
  · exact check_R03e09_02 j
  · exact check_R03e09_03 j
  · exact check_R03e09_04 j
  · exact check_R03e09_05 j
  · exact check_R03e09_06 j
  · exact check_R03e09_07 j
  · exact check_R03e09_08 j
  · exact check_R03e09_09 j
  · exact check_R03e09_10 j
  · exact check_R03e09_11 j
  · exact check_R03e09_12 j
  · exact check_R03e09_13 j
  · exact check_R03e09_14 j
  · exact check_R03e09_15 j
  · exact check_R03e09_16 j
  · exact check_R03e09_17 j
  · exact check_R03e09_18 j
  · exact check_R03e09_19 j
  · exact check_R03e09_20 j
  · exact check_R03e09_21 j

def matrix_R03e09 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03e08)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03p01)

theorem cache_R03e09 : matrix_R03e09=CFSGCoTwoNativeTwentyTwoBaseCaches.I_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches01.R03e08_data CFSGCoTwoNativeTwentyTwoCaches00.R03p01_data CFSGCoTwoNativeTwentyTwoBaseCaches.I_data
    CFSGCoTwoNativeTwentyTwoProducts00.cache_R03e08 CFSGCoTwoNativeTwentyTwoProducts00.cache_R03p01
    (by decide : 22*(2-1)^2<32) checks_R03e09

private theorem check_R04p01_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 0 j%2 := by decide +kernel

private theorem check_R04p01_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 1 j%2 := by decide +kernel

private theorem check_R04p01_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 2 j%2 := by decide +kernel

private theorem check_R04p01_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 3 j%2 := by decide +kernel

private theorem check_R04p01_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 4 j%2 := by decide +kernel

private theorem check_R04p01_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 5 j%2 := by decide +kernel

private theorem check_R04p01_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 6 j%2 := by decide +kernel

private theorem check_R04p01_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 7 j%2 := by decide +kernel

private theorem check_R04p01_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 8 j%2 := by decide +kernel

private theorem check_R04p01_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 9 j%2 := by decide +kernel

private theorem check_R04p01_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 10 j%2 := by decide +kernel

private theorem check_R04p01_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 11 j%2 := by decide +kernel

private theorem check_R04p01_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 12 j%2 := by decide +kernel

private theorem check_R04p01_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 13 j%2 := by decide +kernel

private theorem check_R04p01_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 14 j%2 := by decide +kernel

private theorem check_R04p01_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 15 j%2 := by decide +kernel

private theorem check_R04p01_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 16 j%2 := by decide +kernel

private theorem check_R04p01_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 17 j%2 := by decide +kernel

private theorem check_R04p01_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 18 j%2 := by decide +kernel

private theorem check_R04p01_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 19 j%2 := by decide +kernel

private theorem check_R04p01_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 20 j%2 := by decide +kernel

private theorem check_R04p01_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit 21 j%2 := by decide +kernel

theorem checks_R04p01 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R04p01_00 j
  · exact check_R04p01_01 j
  · exact check_R04p01_02 j
  · exact check_R04p01_03 j
  · exact check_R04p01_04 j
  · exact check_R04p01_05 j
  · exact check_R04p01_06 j
  · exact check_R04p01_07 j
  · exact check_R04p01_08 j
  · exact check_R04p01_09 j
  · exact check_R04p01_10 j
  · exact check_R04p01_11 j
  · exact check_R04p01_12 j
  · exact check_R04p01_13 j
  · exact check_R04p01_14 j
  · exact check_R04p01_15 j
  · exact check_R04p01_16 j
  · exact check_R04p01_17 j
  · exact check_R04p01_18 j
  · exact check_R04p01_19 j
  · exact check_R04p01_20 j
  · exact check_R04p01_21 j

def matrix_R04p01 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B4)

theorem cache_R04p01 : matrix_R04p01=CFSGCoTwoNativeTwentyTwoCaches01.R04p01_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoBaseCaches.B4_data CFSGCoTwoNativeTwentyTwoCaches01.R04p01_data
    CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding CFSGCoTwoNativeTwentyTwoPowerPilot.cache_B4
    (by decide : 22*(2-1)^2<32) checks_R04p01

private theorem check_R04p02_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 0 j%2 := by decide +kernel

private theorem check_R04p02_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 1 j%2 := by decide +kernel

private theorem check_R04p02_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 2 j%2 := by decide +kernel

private theorem check_R04p02_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 3 j%2 := by decide +kernel

private theorem check_R04p02_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 4 j%2 := by decide +kernel

private theorem check_R04p02_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 5 j%2 := by decide +kernel

private theorem check_R04p02_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 6 j%2 := by decide +kernel

private theorem check_R04p02_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 7 j%2 := by decide +kernel

private theorem check_R04p02_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 8 j%2 := by decide +kernel

private theorem check_R04p02_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 9 j%2 := by decide +kernel

private theorem check_R04p02_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 10 j%2 := by decide +kernel

private theorem check_R04p02_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 11 j%2 := by decide +kernel

private theorem check_R04p02_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 12 j%2 := by decide +kernel

private theorem check_R04p02_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 13 j%2 := by decide +kernel

private theorem check_R04p02_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 14 j%2 := by decide +kernel

private theorem check_R04p02_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 15 j%2 := by decide +kernel

private theorem check_R04p02_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 16 j%2 := by decide +kernel

private theorem check_R04p02_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 17 j%2 := by decide +kernel

private theorem check_R04p02_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 18 j%2 := by decide +kernel

private theorem check_R04p02_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 19 j%2 := by decide +kernel

private theorem check_R04p02_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 20 j%2 := by decide +kernel

private theorem check_R04p02_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit 21 j%2 := by decide +kernel

theorem checks_R04p02 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p01_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R04p02_00 j
  · exact check_R04p02_01 j
  · exact check_R04p02_02 j
  · exact check_R04p02_03 j
  · exact check_R04p02_04 j
  · exact check_R04p02_05 j
  · exact check_R04p02_06 j
  · exact check_R04p02_07 j
  · exact check_R04p02_08 j
  · exact check_R04p02_09 j
  · exact check_R04p02_10 j
  · exact check_R04p02_11 j
  · exact check_R04p02_12 j
  · exact check_R04p02_13 j
  · exact check_R04p02_14 j
  · exact check_R04p02_15 j
  · exact check_R04p02_16 j
  · exact check_R04p02_17 j
  · exact check_R04p02_18 j
  · exact check_R04p02_19 j
  · exact check_R04p02_20 j
  · exact check_R04p02_21 j

def matrix_R04p02 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts00.matrix_R04p01)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_R04p02 : matrix_R04p02=CFSGCoTwoNativeTwentyTwoCaches01.R04p02_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches01.R04p01_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches01.R04p02_data
    CFSGCoTwoNativeTwentyTwoProducts00.cache_R04p01 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_R04p02

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts00
