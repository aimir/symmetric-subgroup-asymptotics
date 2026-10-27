import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoBaseCaches
import Mathlib.Tactic.FinCases

/-! Fixed Co2 positive products; every whole matrix entry checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoPowerPilot
open MatrixKroneckerProductReflection

private theorem check_A2_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 0 j%2 := by decide +kernel

private theorem check_A2_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 1 j%2 := by decide +kernel

private theorem check_A2_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 2 j%2 := by decide +kernel

private theorem check_A2_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 3 j%2 := by decide +kernel

private theorem check_A2_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 4 j%2 := by decide +kernel

private theorem check_A2_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 5 j%2 := by decide +kernel

private theorem check_A2_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 6 j%2 := by decide +kernel

private theorem check_A2_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 7 j%2 := by decide +kernel

private theorem check_A2_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 8 j%2 := by decide +kernel

private theorem check_A2_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 9 j%2 := by decide +kernel

private theorem check_A2_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 10 j%2 := by decide +kernel

private theorem check_A2_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 11 j%2 := by decide +kernel

private theorem check_A2_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 12 j%2 := by decide +kernel

private theorem check_A2_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 13 j%2 := by decide +kernel

private theorem check_A2_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 14 j%2 := by decide +kernel

private theorem check_A2_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 15 j%2 := by decide +kernel

private theorem check_A2_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 16 j%2 := by decide +kernel

private theorem check_A2_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 17 j%2 := by decide +kernel

private theorem check_A2_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 18 j%2 := by decide +kernel

private theorem check_A2_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 19 j%2 := by decide +kernel

private theorem check_A2_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 20 j%2 := by decide +kernel

private theorem check_A2_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 21 j%2 := by decide +kernel

theorem checks_A2 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_A2_00 j
  · exact check_A2_01 j
  · exact check_A2_02 j
  · exact check_A2_03 j
  · exact check_A2_04 j
  · exact check_A2_05 j
  · exact check_A2_06 j
  · exact check_A2_07 j
  · exact check_A2_08 j
  · exact check_A2_09 j
  · exact check_A2_10 j
  · exact check_A2_11 j
  · exact check_A2_12 j
  · exact check_A2_13 j
  · exact check_A2_14 j
  · exact check_A2_15 j
  · exact check_A2_16 j
  · exact check_A2_17 j
  · exact check_A2_18 j
  · exact check_A2_19 j
  · exact check_A2_20 j
  · exact check_A2_21 j

def matrix_A2 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_A2 : matrix_A2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoBaseCaches.I_data
    CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_A2

private theorem check_B2_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 0 j%2 := by decide +kernel

private theorem check_B2_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 1 j%2 := by decide +kernel

private theorem check_B2_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 2 j%2 := by decide +kernel

private theorem check_B2_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 3 j%2 := by decide +kernel

private theorem check_B2_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 4 j%2 := by decide +kernel

private theorem check_B2_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 5 j%2 := by decide +kernel

private theorem check_B2_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 6 j%2 := by decide +kernel

private theorem check_B2_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 7 j%2 := by decide +kernel

private theorem check_B2_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 8 j%2 := by decide +kernel

private theorem check_B2_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 9 j%2 := by decide +kernel

private theorem check_B2_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 10 j%2 := by decide +kernel

private theorem check_B2_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 11 j%2 := by decide +kernel

private theorem check_B2_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 12 j%2 := by decide +kernel

private theorem check_B2_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 13 j%2 := by decide +kernel

private theorem check_B2_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 14 j%2 := by decide +kernel

private theorem check_B2_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 15 j%2 := by decide +kernel

private theorem check_B2_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 16 j%2 := by decide +kernel

private theorem check_B2_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 17 j%2 := by decide +kernel

private theorem check_B2_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 18 j%2 := by decide +kernel

private theorem check_B2_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 19 j%2 := by decide +kernel

private theorem check_B2_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 20 j%2 := by decide +kernel

private theorem check_B2_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit 21 j%2 := by decide +kernel

theorem checks_B2 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_B2_00 j
  · exact check_B2_01 j
  · exact check_B2_02 j
  · exact check_B2_03 j
  · exact check_B2_04 j
  · exact check_B2_05 j
  · exact check_B2_06 j
  · exact check_B2_07 j
  · exact check_B2_08 j
  · exact check_B2_09 j
  · exact check_B2_10 j
  · exact check_B2_11 j
  · exact check_B2_12 j
  · exact check_B2_13 j
  · exact check_B2_14 j
  · exact check_B2_15 j
  · exact check_B2_16 j
  · exact check_B2_17 j
  · exact check_B2_18 j
  · exact check_B2_19 j
  · exact check_B2_20 j
  · exact check_B2_21 j

def matrix_B2 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoBaseCaches.matrixB)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixB)

theorem cache_B2 : matrix_B2=CFSGCoTwoNativeTwentyTwoBaseCaches.B2_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoBaseCaches.B_data CFSGCoTwoNativeTwentyTwoBaseCaches.B_data CFSGCoTwoNativeTwentyTwoBaseCaches.B2_data
    CFSGCoTwoNativeTwentyTwoBaseCaches.B_source_binding CFSGCoTwoNativeTwentyTwoBaseCaches.B_source_binding
    (by decide : 22*(2-1)^2<32) checks_B2

private theorem check_B4_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 0 j%2 := by decide +kernel

private theorem check_B4_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 1 j%2 := by decide +kernel

private theorem check_B4_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 2 j%2 := by decide +kernel

private theorem check_B4_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 3 j%2 := by decide +kernel

private theorem check_B4_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 4 j%2 := by decide +kernel

private theorem check_B4_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 5 j%2 := by decide +kernel

private theorem check_B4_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 6 j%2 := by decide +kernel

private theorem check_B4_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 7 j%2 := by decide +kernel

private theorem check_B4_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 8 j%2 := by decide +kernel

private theorem check_B4_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 9 j%2 := by decide +kernel

private theorem check_B4_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 10 j%2 := by decide +kernel

private theorem check_B4_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 11 j%2 := by decide +kernel

private theorem check_B4_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 12 j%2 := by decide +kernel

private theorem check_B4_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 13 j%2 := by decide +kernel

private theorem check_B4_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 14 j%2 := by decide +kernel

private theorem check_B4_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 15 j%2 := by decide +kernel

private theorem check_B4_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 16 j%2 := by decide +kernel

private theorem check_B4_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 17 j%2 := by decide +kernel

private theorem check_B4_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 18 j%2 := by decide +kernel

private theorem check_B4_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 19 j%2 := by decide +kernel

private theorem check_B4_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 20 j%2 := by decide +kernel

private theorem check_B4_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit 21 j%2 := by decide +kernel

theorem checks_B4 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B2_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_B4_00 j
  · exact check_B4_01 j
  · exact check_B4_02 j
  · exact check_B4_03 j
  · exact check_B4_04 j
  · exact check_B4_05 j
  · exact check_B4_06 j
  · exact check_B4_07 j
  · exact check_B4_08 j
  · exact check_B4_09 j
  · exact check_B4_10 j
  · exact check_B4_11 j
  · exact check_B4_12 j
  · exact check_B4_13 j
  · exact check_B4_14 j
  · exact check_B4_15 j
  · exact check_B4_16 j
  · exact check_B4_17 j
  · exact check_B4_18 j
  · exact check_B4_19 j
  · exact check_B4_20 j
  · exact check_B4_21 j

def matrix_B4 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)

theorem cache_B4 : matrix_B4=CFSGCoTwoNativeTwentyTwoBaseCaches.B4_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoBaseCaches.B2_data CFSGCoTwoNativeTwentyTwoBaseCaches.B2_data CFSGCoTwoNativeTwentyTwoBaseCaches.B4_data
    CFSGCoTwoNativeTwentyTwoPowerPilot.cache_B2 CFSGCoTwoNativeTwentyTwoPowerPilot.cache_B2
    (by decide : 22*(2-1)^2<32) checks_B4

private theorem check_B5_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 0 j%2 := by decide +kernel

private theorem check_B5_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 1 j%2 := by decide +kernel

private theorem check_B5_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 2 j%2 := by decide +kernel

private theorem check_B5_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 3 j%2 := by decide +kernel

private theorem check_B5_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 4 j%2 := by decide +kernel

private theorem check_B5_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 5 j%2 := by decide +kernel

private theorem check_B5_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 6 j%2 := by decide +kernel

private theorem check_B5_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 7 j%2 := by decide +kernel

private theorem check_B5_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 8 j%2 := by decide +kernel

private theorem check_B5_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 9 j%2 := by decide +kernel

private theorem check_B5_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 10 j%2 := by decide +kernel

private theorem check_B5_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 11 j%2 := by decide +kernel

private theorem check_B5_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 12 j%2 := by decide +kernel

private theorem check_B5_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 13 j%2 := by decide +kernel

private theorem check_B5_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 14 j%2 := by decide +kernel

private theorem check_B5_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 15 j%2 := by decide +kernel

private theorem check_B5_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 16 j%2 := by decide +kernel

private theorem check_B5_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 17 j%2 := by decide +kernel

private theorem check_B5_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 18 j%2 := by decide +kernel

private theorem check_B5_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 19 j%2 := by decide +kernel

private theorem check_B5_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 20 j%2 := by decide +kernel

private theorem check_B5_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 21 j%2 := by decide +kernel

theorem checks_B5 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.B4_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_B5_00 j
  · exact check_B5_01 j
  · exact check_B5_02 j
  · exact check_B5_03 j
  · exact check_B5_04 j
  · exact check_B5_05 j
  · exact check_B5_06 j
  · exact check_B5_07 j
  · exact check_B5_08 j
  · exact check_B5_09 j
  · exact check_B5_10 j
  · exact check_B5_11 j
  · exact check_B5_12 j
  · exact check_B5_13 j
  · exact check_B5_14 j
  · exact check_B5_15 j
  · exact check_B5_16 j
  · exact check_B5_17 j
  · exact check_B5_18 j
  · exact check_B5_19 j
  · exact check_B5_20 j
  · exact check_B5_21 j

def matrix_B5 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B4)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixB)

theorem cache_B5 : matrix_B5=CFSGCoTwoNativeTwentyTwoBaseCaches.I_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoBaseCaches.B4_data CFSGCoTwoNativeTwentyTwoBaseCaches.B_data CFSGCoTwoNativeTwentyTwoBaseCaches.I_data
    CFSGCoTwoNativeTwentyTwoPowerPilot.cache_B4 CFSGCoTwoNativeTwentyTwoBaseCaches.B_source_binding
    (by decide : 22*(2-1)^2<32) checks_B5

private abbrev A := CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA
private abbrev B := CFSGCoTwoNativeTwentyTwoBaseCaches.matrixB

theorem wholeA_square : A^2=1 := by
  simpa only [pow_two] using
    (show A*A=1 from cache_A2.trans CFSGCoTwoNativeTwentyTwoBaseCaches.identity_binding)

theorem wholeB_fifth : B^5=1 := by
  have h2 : B^2=matrix_B2 := by
    simpa only [pow_two] using (show B*B=matrix_B2 from rfl)
  have h4 : B^4=matrix_B4 := by
    calc
      B^4=B^2*B^2 := pow_add B 2 2
      _=matrix_B2*matrix_B2 := congrArg₂ (fun x y => x*y) h2 h2
      _=matrix_B4 := rfl
  have h5 : B^5=matrix_B5 := by
    calc
      B^5=B^4*B := by simpa only [pow_one] using (pow_add B 4 1)
      _=matrix_B4*B := congrArg (fun x => x*B) h4
      _=matrix_B5 := rfl
  exact h5.trans (cache_B5.trans CFSGCoTwoNativeTwentyTwoBaseCaches.identity_binding)

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoPowerPilot
