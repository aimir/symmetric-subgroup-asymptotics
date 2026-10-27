import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches10
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoBaseCaches
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches11
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches00
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches12
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts05
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoPowerPilot
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts00
import Mathlib.Tactic.FinCases

/-! Fixed Co2 positive products; every whole matrix entry checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts06
open MatrixKroneckerProductReflection

private theorem check_R09e02_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 0 j%2 := by decide +kernel

private theorem check_R09e02_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 1 j%2 := by decide +kernel

private theorem check_R09e02_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 2 j%2 := by decide +kernel

private theorem check_R09e02_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 3 j%2 := by decide +kernel

private theorem check_R09e02_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 4 j%2 := by decide +kernel

private theorem check_R09e02_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 5 j%2 := by decide +kernel

private theorem check_R09e02_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 6 j%2 := by decide +kernel

private theorem check_R09e02_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 7 j%2 := by decide +kernel

private theorem check_R09e02_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 8 j%2 := by decide +kernel

private theorem check_R09e02_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 9 j%2 := by decide +kernel

private theorem check_R09e02_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 10 j%2 := by decide +kernel

private theorem check_R09e02_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 11 j%2 := by decide +kernel

private theorem check_R09e02_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 12 j%2 := by decide +kernel

private theorem check_R09e02_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 13 j%2 := by decide +kernel

private theorem check_R09e02_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 14 j%2 := by decide +kernel

private theorem check_R09e02_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 15 j%2 := by decide +kernel

private theorem check_R09e02_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 16 j%2 := by decide +kernel

private theorem check_R09e02_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 17 j%2 := by decide +kernel

private theorem check_R09e02_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 18 j%2 := by decide +kernel

private theorem check_R09e02_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 19 j%2 := by decide +kernel

private theorem check_R09e02_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 20 j%2 := by decide +kernel

private theorem check_R09e02_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 21 j%2 := by decide +kernel

theorem checks_R09e02 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p11_rowCode i*CFSGCoTwoNativeTwentyTwoCaches10.R09p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R09e02_00 j
  · exact check_R09e02_01 j
  · exact check_R09e02_02 j
  · exact check_R09e02_03 j
  · exact check_R09e02_04 j
  · exact check_R09e02_05 j
  · exact check_R09e02_06 j
  · exact check_R09e02_07 j
  · exact check_R09e02_08 j
  · exact check_R09e02_09 j
  · exact check_R09e02_10 j
  · exact check_R09e02_11 j
  · exact check_R09e02_12 j
  · exact check_R09e02_13 j
  · exact check_R09e02_14 j
  · exact check_R09e02_15 j
  · exact check_R09e02_16 j
  · exact check_R09e02_17 j
  · exact check_R09e02_18 j
  · exact check_R09e02_19 j
  · exact check_R09e02_20 j
  · exact check_R09e02_21 j

def matrix_R09e02 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p11)*(CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p11)

theorem cache_R09e02 : matrix_R09e02=CFSGCoTwoNativeTwentyTwoBaseCaches.I_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches10.R09p11_data CFSGCoTwoNativeTwentyTwoCaches10.R09p11_data CFSGCoTwoNativeTwentyTwoBaseCaches.I_data
    CFSGCoTwoNativeTwentyTwoProducts05.cache_R09p11 CFSGCoTwoNativeTwentyTwoProducts05.cache_R09p11
    (by decide : 22*(2-1)^2<32) checks_R09e02

private theorem check_R10p01_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 0 j%2 := by decide +kernel

private theorem check_R10p01_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 1 j%2 := by decide +kernel

private theorem check_R10p01_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 2 j%2 := by decide +kernel

private theorem check_R10p01_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 3 j%2 := by decide +kernel

private theorem check_R10p01_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 4 j%2 := by decide +kernel

private theorem check_R10p01_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 5 j%2 := by decide +kernel

private theorem check_R10p01_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 6 j%2 := by decide +kernel

private theorem check_R10p01_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 7 j%2 := by decide +kernel

private theorem check_R10p01_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 8 j%2 := by decide +kernel

private theorem check_R10p01_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 9 j%2 := by decide +kernel

private theorem check_R10p01_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 10 j%2 := by decide +kernel

private theorem check_R10p01_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 11 j%2 := by decide +kernel

private theorem check_R10p01_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 12 j%2 := by decide +kernel

private theorem check_R10p01_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 13 j%2 := by decide +kernel

private theorem check_R10p01_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 14 j%2 := by decide +kernel

private theorem check_R10p01_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 15 j%2 := by decide +kernel

private theorem check_R10p01_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 16 j%2 := by decide +kernel

private theorem check_R10p01_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 17 j%2 := by decide +kernel

private theorem check_R10p01_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 18 j%2 := by decide +kernel

private theorem check_R10p01_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 19 j%2 := by decide +kernel

private theorem check_R10p01_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 20 j%2 := by decide +kernel

private theorem check_R10p01_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit 21 j%2 := by decide +kernel

theorem checks_R10p01 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R10p01_00 j
  · exact check_R10p01_01 j
  · exact check_R10p01_02 j
  · exact check_R10p01_03 j
  · exact check_R10p01_04 j
  · exact check_R10p01_05 j
  · exact check_R10p01_06 j
  · exact check_R10p01_07 j
  · exact check_R10p01_08 j
  · exact check_R10p01_09 j
  · exact check_R10p01_10 j
  · exact check_R10p01_11 j
  · exact check_R10p01_12 j
  · exact check_R10p01_13 j
  · exact check_R10p01_14 j
  · exact check_R10p01_15 j
  · exact check_R10p01_16 j
  · exact check_R10p01_17 j
  · exact check_R10p01_18 j
  · exact check_R10p01_19 j
  · exact check_R10p01_20 j
  · exact check_R10p01_21 j

def matrix_R10p01 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixB)

theorem cache_R10p01 : matrix_R10p01=CFSGCoTwoNativeTwentyTwoCaches10.R10p01_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoBaseCaches.B_data CFSGCoTwoNativeTwentyTwoCaches10.R10p01_data
    CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding CFSGCoTwoNativeTwentyTwoBaseCaches.B_source_binding
    (by decide : 22*(2-1)^2<32) checks_R10p01

private theorem check_R10p02_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 0 j%2 := by decide +kernel

private theorem check_R10p02_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 1 j%2 := by decide +kernel

private theorem check_R10p02_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 2 j%2 := by decide +kernel

private theorem check_R10p02_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 3 j%2 := by decide +kernel

private theorem check_R10p02_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 4 j%2 := by decide +kernel

private theorem check_R10p02_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 5 j%2 := by decide +kernel

private theorem check_R10p02_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 6 j%2 := by decide +kernel

private theorem check_R10p02_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 7 j%2 := by decide +kernel

private theorem check_R10p02_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 8 j%2 := by decide +kernel

private theorem check_R10p02_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 9 j%2 := by decide +kernel

private theorem check_R10p02_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 10 j%2 := by decide +kernel

private theorem check_R10p02_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 11 j%2 := by decide +kernel

private theorem check_R10p02_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 12 j%2 := by decide +kernel

private theorem check_R10p02_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 13 j%2 := by decide +kernel

private theorem check_R10p02_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 14 j%2 := by decide +kernel

private theorem check_R10p02_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 15 j%2 := by decide +kernel

private theorem check_R10p02_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 16 j%2 := by decide +kernel

private theorem check_R10p02_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 17 j%2 := by decide +kernel

private theorem check_R10p02_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 18 j%2 := by decide +kernel

private theorem check_R10p02_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 19 j%2 := by decide +kernel

private theorem check_R10p02_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 20 j%2 := by decide +kernel

private theorem check_R10p02_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit 21 j%2 := by decide +kernel

theorem checks_R10p02 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p01_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R10p02_00 j
  · exact check_R10p02_01 j
  · exact check_R10p02_02 j
  · exact check_R10p02_03 j
  · exact check_R10p02_04 j
  · exact check_R10p02_05 j
  · exact check_R10p02_06 j
  · exact check_R10p02_07 j
  · exact check_R10p02_08 j
  · exact check_R10p02_09 j
  · exact check_R10p02_10 j
  · exact check_R10p02_11 j
  · exact check_R10p02_12 j
  · exact check_R10p02_13 j
  · exact check_R10p02_14 j
  · exact check_R10p02_15 j
  · exact check_R10p02_16 j
  · exact check_R10p02_17 j
  · exact check_R10p02_18 j
  · exact check_R10p02_19 j
  · exact check_R10p02_20 j
  · exact check_R10p02_21 j

def matrix_R10p02 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p01)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_R10p02 : matrix_R10p02=CFSGCoTwoNativeTwentyTwoCaches10.R10p02_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches10.R10p01_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches10.R10p02_data
    CFSGCoTwoNativeTwentyTwoProducts06.cache_R10p01 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_R10p02

private theorem check_R10p03_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 0 j%2 := by decide +kernel

private theorem check_R10p03_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 1 j%2 := by decide +kernel

private theorem check_R10p03_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 2 j%2 := by decide +kernel

private theorem check_R10p03_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 3 j%2 := by decide +kernel

private theorem check_R10p03_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 4 j%2 := by decide +kernel

private theorem check_R10p03_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 5 j%2 := by decide +kernel

private theorem check_R10p03_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 6 j%2 := by decide +kernel

private theorem check_R10p03_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 7 j%2 := by decide +kernel

private theorem check_R10p03_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 8 j%2 := by decide +kernel

private theorem check_R10p03_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 9 j%2 := by decide +kernel

private theorem check_R10p03_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 10 j%2 := by decide +kernel

private theorem check_R10p03_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 11 j%2 := by decide +kernel

private theorem check_R10p03_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 12 j%2 := by decide +kernel

private theorem check_R10p03_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 13 j%2 := by decide +kernel

private theorem check_R10p03_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 14 j%2 := by decide +kernel

private theorem check_R10p03_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 15 j%2 := by decide +kernel

private theorem check_R10p03_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 16 j%2 := by decide +kernel

private theorem check_R10p03_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 17 j%2 := by decide +kernel

private theorem check_R10p03_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 18 j%2 := by decide +kernel

private theorem check_R10p03_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 19 j%2 := by decide +kernel

private theorem check_R10p03_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 20 j%2 := by decide +kernel

private theorem check_R10p03_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit 21 j%2 := by decide +kernel

theorem checks_R10p03 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R10p02_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R10p03_00 j
  · exact check_R10p03_01 j
  · exact check_R10p03_02 j
  · exact check_R10p03_03 j
  · exact check_R10p03_04 j
  · exact check_R10p03_05 j
  · exact check_R10p03_06 j
  · exact check_R10p03_07 j
  · exact check_R10p03_08 j
  · exact check_R10p03_09 j
  · exact check_R10p03_10 j
  · exact check_R10p03_11 j
  · exact check_R10p03_12 j
  · exact check_R10p03_13 j
  · exact check_R10p03_14 j
  · exact check_R10p03_15 j
  · exact check_R10p03_16 j
  · exact check_R10p03_17 j
  · exact check_R10p03_18 j
  · exact check_R10p03_19 j
  · exact check_R10p03_20 j
  · exact check_R10p03_21 j

def matrix_R10p03 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p02)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)

theorem cache_R10p03 : matrix_R10p03=CFSGCoTwoNativeTwentyTwoCaches11.R10p03_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches10.R10p02_data CFSGCoTwoNativeTwentyTwoBaseCaches.B2_data CFSGCoTwoNativeTwentyTwoCaches11.R10p03_data
    CFSGCoTwoNativeTwentyTwoProducts06.cache_R10p02 CFSGCoTwoNativeTwentyTwoPowerPilot.cache_B2
    (by decide : 22*(2-1)^2<32) checks_R10p03

private theorem check_R10p04_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 0 j%2 := by decide +kernel

private theorem check_R10p04_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 1 j%2 := by decide +kernel

private theorem check_R10p04_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 2 j%2 := by decide +kernel

private theorem check_R10p04_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 3 j%2 := by decide +kernel

private theorem check_R10p04_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 4 j%2 := by decide +kernel

private theorem check_R10p04_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 5 j%2 := by decide +kernel

private theorem check_R10p04_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 6 j%2 := by decide +kernel

private theorem check_R10p04_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 7 j%2 := by decide +kernel

private theorem check_R10p04_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 8 j%2 := by decide +kernel

private theorem check_R10p04_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 9 j%2 := by decide +kernel

private theorem check_R10p04_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 10 j%2 := by decide +kernel

private theorem check_R10p04_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 11 j%2 := by decide +kernel

private theorem check_R10p04_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 12 j%2 := by decide +kernel

private theorem check_R10p04_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 13 j%2 := by decide +kernel

private theorem check_R10p04_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 14 j%2 := by decide +kernel

private theorem check_R10p04_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 15 j%2 := by decide +kernel

private theorem check_R10p04_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 16 j%2 := by decide +kernel

private theorem check_R10p04_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 17 j%2 := by decide +kernel

private theorem check_R10p04_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 18 j%2 := by decide +kernel

private theorem check_R10p04_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 19 j%2 := by decide +kernel

private theorem check_R10p04_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 20 j%2 := by decide +kernel

private theorem check_R10p04_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit 21 j%2 := by decide +kernel

theorem checks_R10p04 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p03_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R10p04_00 j
  · exact check_R10p04_01 j
  · exact check_R10p04_02 j
  · exact check_R10p04_03 j
  · exact check_R10p04_04 j
  · exact check_R10p04_05 j
  · exact check_R10p04_06 j
  · exact check_R10p04_07 j
  · exact check_R10p04_08 j
  · exact check_R10p04_09 j
  · exact check_R10p04_10 j
  · exact check_R10p04_11 j
  · exact check_R10p04_12 j
  · exact check_R10p04_13 j
  · exact check_R10p04_14 j
  · exact check_R10p04_15 j
  · exact check_R10p04_16 j
  · exact check_R10p04_17 j
  · exact check_R10p04_18 j
  · exact check_R10p04_19 j
  · exact check_R10p04_20 j
  · exact check_R10p04_21 j

def matrix_R10p04 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p03)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_R10p04 : matrix_R10p04=CFSGCoTwoNativeTwentyTwoCaches11.R10p04_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches11.R10p03_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches11.R10p04_data
    CFSGCoTwoNativeTwentyTwoProducts06.cache_R10p03 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_R10p04

private theorem check_R10p05_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 0 j%2 := by decide +kernel

private theorem check_R10p05_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 1 j%2 := by decide +kernel

private theorem check_R10p05_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 2 j%2 := by decide +kernel

private theorem check_R10p05_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 3 j%2 := by decide +kernel

private theorem check_R10p05_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 4 j%2 := by decide +kernel

private theorem check_R10p05_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 5 j%2 := by decide +kernel

private theorem check_R10p05_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 6 j%2 := by decide +kernel

private theorem check_R10p05_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 7 j%2 := by decide +kernel

private theorem check_R10p05_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 8 j%2 := by decide +kernel

private theorem check_R10p05_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 9 j%2 := by decide +kernel

private theorem check_R10p05_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 10 j%2 := by decide +kernel

private theorem check_R10p05_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 11 j%2 := by decide +kernel

private theorem check_R10p05_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 12 j%2 := by decide +kernel

private theorem check_R10p05_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 13 j%2 := by decide +kernel

private theorem check_R10p05_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 14 j%2 := by decide +kernel

private theorem check_R10p05_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 15 j%2 := by decide +kernel

private theorem check_R10p05_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 16 j%2 := by decide +kernel

private theorem check_R10p05_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 17 j%2 := by decide +kernel

private theorem check_R10p05_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 18 j%2 := by decide +kernel

private theorem check_R10p05_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 19 j%2 := by decide +kernel

private theorem check_R10p05_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 20 j%2 := by decide +kernel

private theorem check_R10p05_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit 21 j%2 := by decide +kernel

theorem checks_R10p05 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p04_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R10p05_00 j
  · exact check_R10p05_01 j
  · exact check_R10p05_02 j
  · exact check_R10p05_03 j
  · exact check_R10p05_04 j
  · exact check_R10p05_05 j
  · exact check_R10p05_06 j
  · exact check_R10p05_07 j
  · exact check_R10p05_08 j
  · exact check_R10p05_09 j
  · exact check_R10p05_10 j
  · exact check_R10p05_11 j
  · exact check_R10p05_12 j
  · exact check_R10p05_13 j
  · exact check_R10p05_14 j
  · exact check_R10p05_15 j
  · exact check_R10p05_16 j
  · exact check_R10p05_17 j
  · exact check_R10p05_18 j
  · exact check_R10p05_19 j
  · exact check_R10p05_20 j
  · exact check_R10p05_21 j

def matrix_R10p05 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p04)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B4)

theorem cache_R10p05 : matrix_R10p05=CFSGCoTwoNativeTwentyTwoCaches11.R10p05_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches11.R10p04_data CFSGCoTwoNativeTwentyTwoBaseCaches.B4_data CFSGCoTwoNativeTwentyTwoCaches11.R10p05_data
    CFSGCoTwoNativeTwentyTwoProducts06.cache_R10p04 CFSGCoTwoNativeTwentyTwoPowerPilot.cache_B4
    (by decide : 22*(2-1)^2<32) checks_R10p05

private theorem check_R10p06_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 0 j%2 := by decide +kernel

private theorem check_R10p06_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 1 j%2 := by decide +kernel

private theorem check_R10p06_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 2 j%2 := by decide +kernel

private theorem check_R10p06_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 3 j%2 := by decide +kernel

private theorem check_R10p06_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 4 j%2 := by decide +kernel

private theorem check_R10p06_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 5 j%2 := by decide +kernel

private theorem check_R10p06_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 6 j%2 := by decide +kernel

private theorem check_R10p06_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 7 j%2 := by decide +kernel

private theorem check_R10p06_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 8 j%2 := by decide +kernel

private theorem check_R10p06_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 9 j%2 := by decide +kernel

private theorem check_R10p06_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 10 j%2 := by decide +kernel

private theorem check_R10p06_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 11 j%2 := by decide +kernel

private theorem check_R10p06_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 12 j%2 := by decide +kernel

private theorem check_R10p06_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 13 j%2 := by decide +kernel

private theorem check_R10p06_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 14 j%2 := by decide +kernel

private theorem check_R10p06_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 15 j%2 := by decide +kernel

private theorem check_R10p06_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 16 j%2 := by decide +kernel

private theorem check_R10p06_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 17 j%2 := by decide +kernel

private theorem check_R10p06_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 18 j%2 := by decide +kernel

private theorem check_R10p06_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 19 j%2 := by decide +kernel

private theorem check_R10p06_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 20 j%2 := by decide +kernel

private theorem check_R10p06_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit 21 j%2 := by decide +kernel

theorem checks_R10p06 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p05_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R10p06_00 j
  · exact check_R10p06_01 j
  · exact check_R10p06_02 j
  · exact check_R10p06_03 j
  · exact check_R10p06_04 j
  · exact check_R10p06_05 j
  · exact check_R10p06_06 j
  · exact check_R10p06_07 j
  · exact check_R10p06_08 j
  · exact check_R10p06_09 j
  · exact check_R10p06_10 j
  · exact check_R10p06_11 j
  · exact check_R10p06_12 j
  · exact check_R10p06_13 j
  · exact check_R10p06_14 j
  · exact check_R10p06_15 j
  · exact check_R10p06_16 j
  · exact check_R10p06_17 j
  · exact check_R10p06_18 j
  · exact check_R10p06_19 j
  · exact check_R10p06_20 j
  · exact check_R10p06_21 j

def matrix_R10p06 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p05)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_R10p06 : matrix_R10p06=CFSGCoTwoNativeTwentyTwoCaches11.R10p06_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches11.R10p05_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches11.R10p06_data
    CFSGCoTwoNativeTwentyTwoProducts06.cache_R10p05 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_R10p06

private theorem check_R10p07_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 0 j%2 := by decide +kernel

private theorem check_R10p07_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 1 j%2 := by decide +kernel

private theorem check_R10p07_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 2 j%2 := by decide +kernel

private theorem check_R10p07_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 3 j%2 := by decide +kernel

private theorem check_R10p07_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 4 j%2 := by decide +kernel

private theorem check_R10p07_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 5 j%2 := by decide +kernel

private theorem check_R10p07_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 6 j%2 := by decide +kernel

private theorem check_R10p07_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 7 j%2 := by decide +kernel

private theorem check_R10p07_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 8 j%2 := by decide +kernel

private theorem check_R10p07_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 9 j%2 := by decide +kernel

private theorem check_R10p07_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 10 j%2 := by decide +kernel

private theorem check_R10p07_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 11 j%2 := by decide +kernel

private theorem check_R10p07_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 12 j%2 := by decide +kernel

private theorem check_R10p07_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 13 j%2 := by decide +kernel

private theorem check_R10p07_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 14 j%2 := by decide +kernel

private theorem check_R10p07_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 15 j%2 := by decide +kernel

private theorem check_R10p07_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 16 j%2 := by decide +kernel

private theorem check_R10p07_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 17 j%2 := by decide +kernel

private theorem check_R10p07_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 18 j%2 := by decide +kernel

private theorem check_R10p07_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 19 j%2 := by decide +kernel

private theorem check_R10p07_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 20 j%2 := by decide +kernel

private theorem check_R10p07_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit 21 j%2 := by decide +kernel

theorem checks_R10p07 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches11.R10p06_rowCode i*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R10p07_00 j
  · exact check_R10p07_01 j
  · exact check_R10p07_02 j
  · exact check_R10p07_03 j
  · exact check_R10p07_04 j
  · exact check_R10p07_05 j
  · exact check_R10p07_06 j
  · exact check_R10p07_07 j
  · exact check_R10p07_08 j
  · exact check_R10p07_09 j
  · exact check_R10p07_10 j
  · exact check_R10p07_11 j
  · exact check_R10p07_12 j
  · exact check_R10p07_13 j
  · exact check_R10p07_14 j
  · exact check_R10p07_15 j
  · exact check_R10p07_16 j
  · exact check_R10p07_17 j
  · exact check_R10p07_18 j
  · exact check_R10p07_19 j
  · exact check_R10p07_20 j
  · exact check_R10p07_21 j

def matrix_R10p07 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p06)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_B3)

theorem cache_R10p07 : matrix_R10p07=CFSGCoTwoNativeTwentyTwoCaches12.R10p07_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches11.R10p06_data CFSGCoTwoNativeTwentyTwoCaches00.B3_data CFSGCoTwoNativeTwentyTwoCaches12.R10p07_data
    CFSGCoTwoNativeTwentyTwoProducts06.cache_R10p06 CFSGCoTwoNativeTwentyTwoProducts00.cache_B3
    (by decide : 22*(2-1)^2<32) checks_R10p07

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts06
