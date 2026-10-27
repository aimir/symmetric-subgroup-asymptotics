import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches12
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoBaseCaches
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches02
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches13
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts06
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts01
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoPowerPilot
import Mathlib.Tactic.FinCases

/-! Fixed Co2 positive products; every whole matrix entry checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts07
open MatrixKroneckerProductReflection

private theorem check_R10e02_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 0 j%2 := by decide +kernel

private theorem check_R10e02_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 1 j%2 := by decide +kernel

private theorem check_R10e02_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 2 j%2 := by decide +kernel

private theorem check_R10e02_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 3 j%2 := by decide +kernel

private theorem check_R10e02_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 4 j%2 := by decide +kernel

private theorem check_R10e02_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 5 j%2 := by decide +kernel

private theorem check_R10e02_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 6 j%2 := by decide +kernel

private theorem check_R10e02_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 7 j%2 := by decide +kernel

private theorem check_R10e02_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 8 j%2 := by decide +kernel

private theorem check_R10e02_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 9 j%2 := by decide +kernel

private theorem check_R10e02_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 10 j%2 := by decide +kernel

private theorem check_R10e02_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 11 j%2 := by decide +kernel

private theorem check_R10e02_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 12 j%2 := by decide +kernel

private theorem check_R10e02_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 13 j%2 := by decide +kernel

private theorem check_R10e02_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 14 j%2 := by decide +kernel

private theorem check_R10e02_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 15 j%2 := by decide +kernel

private theorem check_R10e02_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 16 j%2 := by decide +kernel

private theorem check_R10e02_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 17 j%2 := by decide +kernel

private theorem check_R10e02_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 18 j%2 := by decide +kernel

private theorem check_R10e02_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 19 j%2 := by decide +kernel

private theorem check_R10e02_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 20 j%2 := by decide +kernel

private theorem check_R10e02_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit 21 j%2 := by decide +kernel

theorem checks_R10e02 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10p07_rowCode i*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R10e02_00 j
  · exact check_R10e02_01 j
  · exact check_R10e02_02 j
  · exact check_R10e02_03 j
  · exact check_R10e02_04 j
  · exact check_R10e02_05 j
  · exact check_R10e02_06 j
  · exact check_R10e02_07 j
  · exact check_R10e02_08 j
  · exact check_R10e02_09 j
  · exact check_R10e02_10 j
  · exact check_R10e02_11 j
  · exact check_R10e02_12 j
  · exact check_R10e02_13 j
  · exact check_R10e02_14 j
  · exact check_R10e02_15 j
  · exact check_R10e02_16 j
  · exact check_R10e02_17 j
  · exact check_R10e02_18 j
  · exact check_R10e02_19 j
  · exact check_R10e02_20 j
  · exact check_R10e02_21 j

def matrix_R10e02 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p07)*(CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p07)

theorem cache_R10e02 : matrix_R10e02=CFSGCoTwoNativeTwentyTwoCaches12.R10e02_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches12.R10p07_data CFSGCoTwoNativeTwentyTwoCaches12.R10p07_data CFSGCoTwoNativeTwentyTwoCaches12.R10e02_data
    CFSGCoTwoNativeTwentyTwoProducts06.cache_R10p07 CFSGCoTwoNativeTwentyTwoProducts06.cache_R10p07
    (by decide : 22*(2-1)^2<32) checks_R10e02

private theorem check_R10e04_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 0 j%2 := by decide +kernel

private theorem check_R10e04_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 1 j%2 := by decide +kernel

private theorem check_R10e04_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 2 j%2 := by decide +kernel

private theorem check_R10e04_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 3 j%2 := by decide +kernel

private theorem check_R10e04_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 4 j%2 := by decide +kernel

private theorem check_R10e04_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 5 j%2 := by decide +kernel

private theorem check_R10e04_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 6 j%2 := by decide +kernel

private theorem check_R10e04_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 7 j%2 := by decide +kernel

private theorem check_R10e04_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 8 j%2 := by decide +kernel

private theorem check_R10e04_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 9 j%2 := by decide +kernel

private theorem check_R10e04_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 10 j%2 := by decide +kernel

private theorem check_R10e04_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 11 j%2 := by decide +kernel

private theorem check_R10e04_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 12 j%2 := by decide +kernel

private theorem check_R10e04_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 13 j%2 := by decide +kernel

private theorem check_R10e04_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 14 j%2 := by decide +kernel

private theorem check_R10e04_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 15 j%2 := by decide +kernel

private theorem check_R10e04_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 16 j%2 := by decide +kernel

private theorem check_R10e04_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 17 j%2 := by decide +kernel

private theorem check_R10e04_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 18 j%2 := by decide +kernel

private theorem check_R10e04_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 19 j%2 := by decide +kernel

private theorem check_R10e04_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 20 j%2 := by decide +kernel

private theorem check_R10e04_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit 21 j%2 := by decide +kernel

theorem checks_R10e04 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e02_rowCode i*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R10e04_00 j
  · exact check_R10e04_01 j
  · exact check_R10e04_02 j
  · exact check_R10e04_03 j
  · exact check_R10e04_04 j
  · exact check_R10e04_05 j
  · exact check_R10e04_06 j
  · exact check_R10e04_07 j
  · exact check_R10e04_08 j
  · exact check_R10e04_09 j
  · exact check_R10e04_10 j
  · exact check_R10e04_11 j
  · exact check_R10e04_12 j
  · exact check_R10e04_13 j
  · exact check_R10e04_14 j
  · exact check_R10e04_15 j
  · exact check_R10e04_16 j
  · exact check_R10e04_17 j
  · exact check_R10e04_18 j
  · exact check_R10e04_19 j
  · exact check_R10e04_20 j
  · exact check_R10e04_21 j

def matrix_R10e04 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts07.matrix_R10e02)*(CFSGCoTwoNativeTwentyTwoProducts07.matrix_R10e02)

theorem cache_R10e04 : matrix_R10e04=CFSGCoTwoNativeTwentyTwoCaches12.R10e04_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches12.R10e02_data CFSGCoTwoNativeTwentyTwoCaches12.R10e02_data CFSGCoTwoNativeTwentyTwoCaches12.R10e04_data
    CFSGCoTwoNativeTwentyTwoProducts07.cache_R10e02 CFSGCoTwoNativeTwentyTwoProducts07.cache_R10e02
    (by decide : 22*(2-1)^2<32) checks_R10e04

private theorem check_R10e06_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 0 j%2 := by decide +kernel

private theorem check_R10e06_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 1 j%2 := by decide +kernel

private theorem check_R10e06_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 2 j%2 := by decide +kernel

private theorem check_R10e06_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 3 j%2 := by decide +kernel

private theorem check_R10e06_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 4 j%2 := by decide +kernel

private theorem check_R10e06_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 5 j%2 := by decide +kernel

private theorem check_R10e06_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 6 j%2 := by decide +kernel

private theorem check_R10e06_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 7 j%2 := by decide +kernel

private theorem check_R10e06_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 8 j%2 := by decide +kernel

private theorem check_R10e06_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 9 j%2 := by decide +kernel

private theorem check_R10e06_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 10 j%2 := by decide +kernel

private theorem check_R10e06_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 11 j%2 := by decide +kernel

private theorem check_R10e06_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 12 j%2 := by decide +kernel

private theorem check_R10e06_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 13 j%2 := by decide +kernel

private theorem check_R10e06_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 14 j%2 := by decide +kernel

private theorem check_R10e06_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 15 j%2 := by decide +kernel

private theorem check_R10e06_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 16 j%2 := by decide +kernel

private theorem check_R10e06_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 17 j%2 := by decide +kernel

private theorem check_R10e06_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 18 j%2 := by decide +kernel

private theorem check_R10e06_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 19 j%2 := by decide +kernel

private theorem check_R10e06_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 20 j%2 := by decide +kernel

private theorem check_R10e06_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit 21 j%2 := by decide +kernel

theorem checks_R10e06 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e04_rowCode i*CFSGCoTwoNativeTwentyTwoCaches12.R10e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R10e06_00 j
  · exact check_R10e06_01 j
  · exact check_R10e06_02 j
  · exact check_R10e06_03 j
  · exact check_R10e06_04 j
  · exact check_R10e06_05 j
  · exact check_R10e06_06 j
  · exact check_R10e06_07 j
  · exact check_R10e06_08 j
  · exact check_R10e06_09 j
  · exact check_R10e06_10 j
  · exact check_R10e06_11 j
  · exact check_R10e06_12 j
  · exact check_R10e06_13 j
  · exact check_R10e06_14 j
  · exact check_R10e06_15 j
  · exact check_R10e06_16 j
  · exact check_R10e06_17 j
  · exact check_R10e06_18 j
  · exact check_R10e06_19 j
  · exact check_R10e06_20 j
  · exact check_R10e06_21 j

def matrix_R10e06 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts07.matrix_R10e04)*(CFSGCoTwoNativeTwentyTwoProducts07.matrix_R10e02)

theorem cache_R10e06 : matrix_R10e06=CFSGCoTwoNativeTwentyTwoCaches12.R10e06_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches12.R10e04_data CFSGCoTwoNativeTwentyTwoCaches12.R10e02_data CFSGCoTwoNativeTwentyTwoCaches12.R10e06_data
    CFSGCoTwoNativeTwentyTwoProducts07.cache_R10e04 CFSGCoTwoNativeTwentyTwoProducts07.cache_R10e02
    (by decide : 22*(2-1)^2<32) checks_R10e06

private theorem check_R10e07_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 0 j%2 := by decide +kernel

private theorem check_R10e07_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 1 j%2 := by decide +kernel

private theorem check_R10e07_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 2 j%2 := by decide +kernel

private theorem check_R10e07_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 3 j%2 := by decide +kernel

private theorem check_R10e07_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 4 j%2 := by decide +kernel

private theorem check_R10e07_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 5 j%2 := by decide +kernel

private theorem check_R10e07_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 6 j%2 := by decide +kernel

private theorem check_R10e07_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 7 j%2 := by decide +kernel

private theorem check_R10e07_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 8 j%2 := by decide +kernel

private theorem check_R10e07_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 9 j%2 := by decide +kernel

private theorem check_R10e07_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 10 j%2 := by decide +kernel

private theorem check_R10e07_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 11 j%2 := by decide +kernel

private theorem check_R10e07_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 12 j%2 := by decide +kernel

private theorem check_R10e07_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 13 j%2 := by decide +kernel

private theorem check_R10e07_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 14 j%2 := by decide +kernel

private theorem check_R10e07_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 15 j%2 := by decide +kernel

private theorem check_R10e07_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 16 j%2 := by decide +kernel

private theorem check_R10e07_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 17 j%2 := by decide +kernel

private theorem check_R10e07_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 18 j%2 := by decide +kernel

private theorem check_R10e07_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 19 j%2 := by decide +kernel

private theorem check_R10e07_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 20 j%2 := by decide +kernel

private theorem check_R10e07_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 21 j%2 := by decide +kernel

theorem checks_R10e07 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches12.R10e06_rowCode i*CFSGCoTwoNativeTwentyTwoCaches12.R10p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R10e07_00 j
  · exact check_R10e07_01 j
  · exact check_R10e07_02 j
  · exact check_R10e07_03 j
  · exact check_R10e07_04 j
  · exact check_R10e07_05 j
  · exact check_R10e07_06 j
  · exact check_R10e07_07 j
  · exact check_R10e07_08 j
  · exact check_R10e07_09 j
  · exact check_R10e07_10 j
  · exact check_R10e07_11 j
  · exact check_R10e07_12 j
  · exact check_R10e07_13 j
  · exact check_R10e07_14 j
  · exact check_R10e07_15 j
  · exact check_R10e07_16 j
  · exact check_R10e07_17 j
  · exact check_R10e07_18 j
  · exact check_R10e07_19 j
  · exact check_R10e07_20 j
  · exact check_R10e07_21 j

def matrix_R10e07 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts07.matrix_R10e06)*(CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p07)

theorem cache_R10e07 : matrix_R10e07=CFSGCoTwoNativeTwentyTwoBaseCaches.I_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches12.R10e06_data CFSGCoTwoNativeTwentyTwoCaches12.R10p07_data CFSGCoTwoNativeTwentyTwoBaseCaches.I_data
    CFSGCoTwoNativeTwentyTwoProducts07.cache_R10e06 CFSGCoTwoNativeTwentyTwoProducts06.cache_R10p07
    (by decide : 22*(2-1)^2<32) checks_R10e07

private theorem check_Wp03_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 0 j%2 := by decide +kernel

private theorem check_Wp03_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 1 j%2 := by decide +kernel

private theorem check_Wp03_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 2 j%2 := by decide +kernel

private theorem check_Wp03_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 3 j%2 := by decide +kernel

private theorem check_Wp03_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 4 j%2 := by decide +kernel

private theorem check_Wp03_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 5 j%2 := by decide +kernel

private theorem check_Wp03_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 6 j%2 := by decide +kernel

private theorem check_Wp03_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 7 j%2 := by decide +kernel

private theorem check_Wp03_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 8 j%2 := by decide +kernel

private theorem check_Wp03_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 9 j%2 := by decide +kernel

private theorem check_Wp03_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 10 j%2 := by decide +kernel

private theorem check_Wp03_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 11 j%2 := by decide +kernel

private theorem check_Wp03_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 12 j%2 := by decide +kernel

private theorem check_Wp03_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 13 j%2 := by decide +kernel

private theorem check_Wp03_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 14 j%2 := by decide +kernel

private theorem check_Wp03_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 15 j%2 := by decide +kernel

private theorem check_Wp03_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 16 j%2 := by decide +kernel

private theorem check_Wp03_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 17 j%2 := by decide +kernel

private theorem check_Wp03_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 18 j%2 := by decide +kernel

private theorem check_Wp03_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 19 j%2 := by decide +kernel

private theorem check_Wp03_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 20 j%2 := by decide +kernel

private theorem check_Wp03_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit 21 j%2 := by decide +kernel

theorem checks_Wp03 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_Wp03_00 j
  · exact check_Wp03_01 j
  · exact check_Wp03_02 j
  · exact check_Wp03_03 j
  · exact check_Wp03_04 j
  · exact check_Wp03_05 j
  · exact check_Wp03_06 j
  · exact check_Wp03_07 j
  · exact check_Wp03_08 j
  · exact check_Wp03_09 j
  · exact check_Wp03_10 j
  · exact check_Wp03_11 j
  · exact check_Wp03_12 j
  · exact check_Wp03_13 j
  · exact check_Wp03_14 j
  · exact check_Wp03_15 j
  · exact check_Wp03_16 j
  · exact check_Wp03_17 j
  · exact check_Wp03_18 j
  · exact check_Wp03_19 j
  · exact check_Wp03_20 j
  · exact check_Wp03_21 j

def matrix_Wp03 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05p02)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixB)

theorem cache_Wp03 : matrix_Wp03=CFSGCoTwoNativeTwentyTwoCaches13.Wp03_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches02.R05p02_data CFSGCoTwoNativeTwentyTwoBaseCaches.B_data CFSGCoTwoNativeTwentyTwoCaches13.Wp03_data
    CFSGCoTwoNativeTwentyTwoProducts01.cache_R05p02 CFSGCoTwoNativeTwentyTwoBaseCaches.B_source_binding
    (by decide : 22*(2-1)^2<32) checks_Wp03

private theorem check_Wp04_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 0 j%2 := by decide +kernel

private theorem check_Wp04_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 1 j%2 := by decide +kernel

private theorem check_Wp04_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 2 j%2 := by decide +kernel

private theorem check_Wp04_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 3 j%2 := by decide +kernel

private theorem check_Wp04_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 4 j%2 := by decide +kernel

private theorem check_Wp04_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 5 j%2 := by decide +kernel

private theorem check_Wp04_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 6 j%2 := by decide +kernel

private theorem check_Wp04_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 7 j%2 := by decide +kernel

private theorem check_Wp04_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 8 j%2 := by decide +kernel

private theorem check_Wp04_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 9 j%2 := by decide +kernel

private theorem check_Wp04_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 10 j%2 := by decide +kernel

private theorem check_Wp04_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 11 j%2 := by decide +kernel

private theorem check_Wp04_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 12 j%2 := by decide +kernel

private theorem check_Wp04_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 13 j%2 := by decide +kernel

private theorem check_Wp04_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 14 j%2 := by decide +kernel

private theorem check_Wp04_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 15 j%2 := by decide +kernel

private theorem check_Wp04_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 16 j%2 := by decide +kernel

private theorem check_Wp04_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 17 j%2 := by decide +kernel

private theorem check_Wp04_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 18 j%2 := by decide +kernel

private theorem check_Wp04_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 19 j%2 := by decide +kernel

private theorem check_Wp04_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 20 j%2 := by decide +kernel

private theorem check_Wp04_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit 21 j%2 := by decide +kernel

theorem checks_Wp04 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp03_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_Wp04_00 j
  · exact check_Wp04_01 j
  · exact check_Wp04_02 j
  · exact check_Wp04_03 j
  · exact check_Wp04_04 j
  · exact check_Wp04_05 j
  · exact check_Wp04_06 j
  · exact check_Wp04_07 j
  · exact check_Wp04_08 j
  · exact check_Wp04_09 j
  · exact check_Wp04_10 j
  · exact check_Wp04_11 j
  · exact check_Wp04_12 j
  · exact check_Wp04_13 j
  · exact check_Wp04_14 j
  · exact check_Wp04_15 j
  · exact check_Wp04_16 j
  · exact check_Wp04_17 j
  · exact check_Wp04_18 j
  · exact check_Wp04_19 j
  · exact check_Wp04_20 j
  · exact check_Wp04_21 j

def matrix_Wp04 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts07.matrix_Wp03)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_Wp04 : matrix_Wp04=CFSGCoTwoNativeTwentyTwoCaches13.Wp04_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches13.Wp03_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches13.Wp04_data
    CFSGCoTwoNativeTwentyTwoProducts07.cache_Wp03 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_Wp04

private theorem check_Wp05_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 0 j%2 := by decide +kernel

private theorem check_Wp05_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 1 j%2 := by decide +kernel

private theorem check_Wp05_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 2 j%2 := by decide +kernel

private theorem check_Wp05_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 3 j%2 := by decide +kernel

private theorem check_Wp05_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 4 j%2 := by decide +kernel

private theorem check_Wp05_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 5 j%2 := by decide +kernel

private theorem check_Wp05_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 6 j%2 := by decide +kernel

private theorem check_Wp05_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 7 j%2 := by decide +kernel

private theorem check_Wp05_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 8 j%2 := by decide +kernel

private theorem check_Wp05_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 9 j%2 := by decide +kernel

private theorem check_Wp05_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 10 j%2 := by decide +kernel

private theorem check_Wp05_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 11 j%2 := by decide +kernel

private theorem check_Wp05_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 12 j%2 := by decide +kernel

private theorem check_Wp05_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 13 j%2 := by decide +kernel

private theorem check_Wp05_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 14 j%2 := by decide +kernel

private theorem check_Wp05_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 15 j%2 := by decide +kernel

private theorem check_Wp05_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 16 j%2 := by decide +kernel

private theorem check_Wp05_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 17 j%2 := by decide +kernel

private theorem check_Wp05_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 18 j%2 := by decide +kernel

private theorem check_Wp05_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 19 j%2 := by decide +kernel

private theorem check_Wp05_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 20 j%2 := by decide +kernel

private theorem check_Wp05_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit 21 j%2 := by decide +kernel

theorem checks_Wp05 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches13.Wp04_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_Wp05_00 j
  · exact check_Wp05_01 j
  · exact check_Wp05_02 j
  · exact check_Wp05_03 j
  · exact check_Wp05_04 j
  · exact check_Wp05_05 j
  · exact check_Wp05_06 j
  · exact check_Wp05_07 j
  · exact check_Wp05_08 j
  · exact check_Wp05_09 j
  · exact check_Wp05_10 j
  · exact check_Wp05_11 j
  · exact check_Wp05_12 j
  · exact check_Wp05_13 j
  · exact check_Wp05_14 j
  · exact check_Wp05_15 j
  · exact check_Wp05_16 j
  · exact check_Wp05_17 j
  · exact check_Wp05_18 j
  · exact check_Wp05_19 j
  · exact check_Wp05_20 j
  · exact check_Wp05_21 j

def matrix_Wp05 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts07.matrix_Wp04)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)

theorem cache_Wp05 : matrix_Wp05=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches13.Wp04_data CFSGCoTwoNativeTwentyTwoBaseCaches.B2_data CFSGCoTwoNativeTwentyTwoCaches13.Wp05_data
    CFSGCoTwoNativeTwentyTwoProducts07.cache_Wp04 CFSGCoTwoNativeTwentyTwoPowerPilot.cache_B2
    (by decide : 22*(2-1)^2<32) checks_Wp05

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts07
