import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches01
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoBaseCaches
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches02
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches00
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches03
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts00
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoPowerPilot
import Mathlib.Tactic.FinCases

/-! Fixed Co2 positive products; every whole matrix entry checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts01
open MatrixKroneckerProductReflection

private theorem check_R04p03_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 0 j%2 := by decide +kernel

private theorem check_R04p03_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 1 j%2 := by decide +kernel

private theorem check_R04p03_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 2 j%2 := by decide +kernel

private theorem check_R04p03_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 3 j%2 := by decide +kernel

private theorem check_R04p03_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 4 j%2 := by decide +kernel

private theorem check_R04p03_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 5 j%2 := by decide +kernel

private theorem check_R04p03_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 6 j%2 := by decide +kernel

private theorem check_R04p03_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 7 j%2 := by decide +kernel

private theorem check_R04p03_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 8 j%2 := by decide +kernel

private theorem check_R04p03_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 9 j%2 := by decide +kernel

private theorem check_R04p03_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 10 j%2 := by decide +kernel

private theorem check_R04p03_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 11 j%2 := by decide +kernel

private theorem check_R04p03_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 12 j%2 := by decide +kernel

private theorem check_R04p03_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 13 j%2 := by decide +kernel

private theorem check_R04p03_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 14 j%2 := by decide +kernel

private theorem check_R04p03_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 15 j%2 := by decide +kernel

private theorem check_R04p03_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 16 j%2 := by decide +kernel

private theorem check_R04p03_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 17 j%2 := by decide +kernel

private theorem check_R04p03_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 18 j%2 := by decide +kernel

private theorem check_R04p03_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 19 j%2 := by decide +kernel

private theorem check_R04p03_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 20 j%2 := by decide +kernel

private theorem check_R04p03_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit 21 j%2 := by decide +kernel

theorem checks_R04p03 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R04p03_00 j
  · exact check_R04p03_01 j
  · exact check_R04p03_02 j
  · exact check_R04p03_03 j
  · exact check_R04p03_04 j
  · exact check_R04p03_05 j
  · exact check_R04p03_06 j
  · exact check_R04p03_07 j
  · exact check_R04p03_08 j
  · exact check_R04p03_09 j
  · exact check_R04p03_10 j
  · exact check_R04p03_11 j
  · exact check_R04p03_12 j
  · exact check_R04p03_13 j
  · exact check_R04p03_14 j
  · exact check_R04p03_15 j
  · exact check_R04p03_16 j
  · exact check_R04p03_17 j
  · exact check_R04p03_18 j
  · exact check_R04p03_19 j
  · exact check_R04p03_20 j
  · exact check_R04p03_21 j

def matrix_R04p03 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts00.matrix_R04p02)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixB)

theorem cache_R04p03 : matrix_R04p03=CFSGCoTwoNativeTwentyTwoCaches01.R04p03_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches01.R04p02_data CFSGCoTwoNativeTwentyTwoBaseCaches.B_data CFSGCoTwoNativeTwentyTwoCaches01.R04p03_data
    CFSGCoTwoNativeTwentyTwoProducts00.cache_R04p02 CFSGCoTwoNativeTwentyTwoBaseCaches.B_source_binding
    (by decide : 22*(2-1)^2<32) checks_R04p03

private theorem check_R04e02_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 0 j%2 := by decide +kernel

private theorem check_R04e02_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 1 j%2 := by decide +kernel

private theorem check_R04e02_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 2 j%2 := by decide +kernel

private theorem check_R04e02_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 3 j%2 := by decide +kernel

private theorem check_R04e02_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 4 j%2 := by decide +kernel

private theorem check_R04e02_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 5 j%2 := by decide +kernel

private theorem check_R04e02_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 6 j%2 := by decide +kernel

private theorem check_R04e02_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 7 j%2 := by decide +kernel

private theorem check_R04e02_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 8 j%2 := by decide +kernel

private theorem check_R04e02_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 9 j%2 := by decide +kernel

private theorem check_R04e02_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 10 j%2 := by decide +kernel

private theorem check_R04e02_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 11 j%2 := by decide +kernel

private theorem check_R04e02_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 12 j%2 := by decide +kernel

private theorem check_R04e02_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 13 j%2 := by decide +kernel

private theorem check_R04e02_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 14 j%2 := by decide +kernel

private theorem check_R04e02_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 15 j%2 := by decide +kernel

private theorem check_R04e02_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 16 j%2 := by decide +kernel

private theorem check_R04e02_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 17 j%2 := by decide +kernel

private theorem check_R04e02_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 18 j%2 := by decide +kernel

private theorem check_R04e02_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 19 j%2 := by decide +kernel

private theorem check_R04e02_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 20 j%2 := by decide +kernel

private theorem check_R04e02_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit 21 j%2 := by decide +kernel

theorem checks_R04e02 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p03_rowCode i*CFSGCoTwoNativeTwentyTwoCaches01.R04p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R04e02_00 j
  · exact check_R04e02_01 j
  · exact check_R04e02_02 j
  · exact check_R04e02_03 j
  · exact check_R04e02_04 j
  · exact check_R04e02_05 j
  · exact check_R04e02_06 j
  · exact check_R04e02_07 j
  · exact check_R04e02_08 j
  · exact check_R04e02_09 j
  · exact check_R04e02_10 j
  · exact check_R04e02_11 j
  · exact check_R04e02_12 j
  · exact check_R04e02_13 j
  · exact check_R04e02_14 j
  · exact check_R04e02_15 j
  · exact check_R04e02_16 j
  · exact check_R04e02_17 j
  · exact check_R04e02_18 j
  · exact check_R04e02_19 j
  · exact check_R04e02_20 j
  · exact check_R04e02_21 j

def matrix_R04e02 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts01.matrix_R04p03)*(CFSGCoTwoNativeTwentyTwoProducts01.matrix_R04p03)

theorem cache_R04e02 : matrix_R04e02=CFSGCoTwoNativeTwentyTwoCaches02.R04e02_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches01.R04p03_data CFSGCoTwoNativeTwentyTwoCaches01.R04p03_data CFSGCoTwoNativeTwentyTwoCaches02.R04e02_data
    CFSGCoTwoNativeTwentyTwoProducts01.cache_R04p03 CFSGCoTwoNativeTwentyTwoProducts01.cache_R04p03
    (by decide : 22*(2-1)^2<32) checks_R04e02

private theorem check_R04e04_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 0 j%2 := by decide +kernel

private theorem check_R04e04_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 1 j%2 := by decide +kernel

private theorem check_R04e04_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 2 j%2 := by decide +kernel

private theorem check_R04e04_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 3 j%2 := by decide +kernel

private theorem check_R04e04_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 4 j%2 := by decide +kernel

private theorem check_R04e04_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 5 j%2 := by decide +kernel

private theorem check_R04e04_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 6 j%2 := by decide +kernel

private theorem check_R04e04_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 7 j%2 := by decide +kernel

private theorem check_R04e04_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 8 j%2 := by decide +kernel

private theorem check_R04e04_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 9 j%2 := by decide +kernel

private theorem check_R04e04_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 10 j%2 := by decide +kernel

private theorem check_R04e04_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 11 j%2 := by decide +kernel

private theorem check_R04e04_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 12 j%2 := by decide +kernel

private theorem check_R04e04_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 13 j%2 := by decide +kernel

private theorem check_R04e04_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 14 j%2 := by decide +kernel

private theorem check_R04e04_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 15 j%2 := by decide +kernel

private theorem check_R04e04_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 16 j%2 := by decide +kernel

private theorem check_R04e04_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 17 j%2 := by decide +kernel

private theorem check_R04e04_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 18 j%2 := by decide +kernel

private theorem check_R04e04_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 19 j%2 := by decide +kernel

private theorem check_R04e04_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 20 j%2 := by decide +kernel

private theorem check_R04e04_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 21 j%2 := by decide +kernel

theorem checks_R04e04 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R04e02_rowCode i*CFSGCoTwoNativeTwentyTwoCaches02.R04e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R04e04_00 j
  · exact check_R04e04_01 j
  · exact check_R04e04_02 j
  · exact check_R04e04_03 j
  · exact check_R04e04_04 j
  · exact check_R04e04_05 j
  · exact check_R04e04_06 j
  · exact check_R04e04_07 j
  · exact check_R04e04_08 j
  · exact check_R04e04_09 j
  · exact check_R04e04_10 j
  · exact check_R04e04_11 j
  · exact check_R04e04_12 j
  · exact check_R04e04_13 j
  · exact check_R04e04_14 j
  · exact check_R04e04_15 j
  · exact check_R04e04_16 j
  · exact check_R04e04_17 j
  · exact check_R04e04_18 j
  · exact check_R04e04_19 j
  · exact check_R04e04_20 j
  · exact check_R04e04_21 j

def matrix_R04e04 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts01.matrix_R04e02)*(CFSGCoTwoNativeTwentyTwoProducts01.matrix_R04e02)

theorem cache_R04e04 : matrix_R04e04=CFSGCoTwoNativeTwentyTwoBaseCaches.I_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches02.R04e02_data CFSGCoTwoNativeTwentyTwoCaches02.R04e02_data CFSGCoTwoNativeTwentyTwoBaseCaches.I_data
    CFSGCoTwoNativeTwentyTwoProducts01.cache_R04e02 CFSGCoTwoNativeTwentyTwoProducts01.cache_R04e02
    (by decide : 22*(2-1)^2<32) checks_R04e04

private theorem check_R05p01_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 0 j%2 := by decide +kernel

private theorem check_R05p01_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 1 j%2 := by decide +kernel

private theorem check_R05p01_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 2 j%2 := by decide +kernel

private theorem check_R05p01_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 3 j%2 := by decide +kernel

private theorem check_R05p01_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 4 j%2 := by decide +kernel

private theorem check_R05p01_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 5 j%2 := by decide +kernel

private theorem check_R05p01_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 6 j%2 := by decide +kernel

private theorem check_R05p01_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 7 j%2 := by decide +kernel

private theorem check_R05p01_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 8 j%2 := by decide +kernel

private theorem check_R05p01_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 9 j%2 := by decide +kernel

private theorem check_R05p01_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 10 j%2 := by decide +kernel

private theorem check_R05p01_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 11 j%2 := by decide +kernel

private theorem check_R05p01_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 12 j%2 := by decide +kernel

private theorem check_R05p01_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 13 j%2 := by decide +kernel

private theorem check_R05p01_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 14 j%2 := by decide +kernel

private theorem check_R05p01_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 15 j%2 := by decide +kernel

private theorem check_R05p01_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 16 j%2 := by decide +kernel

private theorem check_R05p01_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 17 j%2 := by decide +kernel

private theorem check_R05p01_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 18 j%2 := by decide +kernel

private theorem check_R05p01_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 19 j%2 := by decide +kernel

private theorem check_R05p01_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 20 j%2 := by decide +kernel

private theorem check_R05p01_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit 21 j%2 := by decide +kernel

theorem checks_R05p01 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoBaseCaches.A_rowCode i*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R05p01_00 j
  · exact check_R05p01_01 j
  · exact check_R05p01_02 j
  · exact check_R05p01_03 j
  · exact check_R05p01_04 j
  · exact check_R05p01_05 j
  · exact check_R05p01_06 j
  · exact check_R05p01_07 j
  · exact check_R05p01_08 j
  · exact check_R05p01_09 j
  · exact check_R05p01_10 j
  · exact check_R05p01_11 j
  · exact check_R05p01_12 j
  · exact check_R05p01_13 j
  · exact check_R05p01_14 j
  · exact check_R05p01_15 j
  · exact check_R05p01_16 j
  · exact check_R05p01_17 j
  · exact check_R05p01_18 j
  · exact check_R05p01_19 j
  · exact check_R05p01_20 j
  · exact check_R05p01_21 j

def matrix_R05p01 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_B3)

theorem cache_R05p01 : matrix_R05p01=CFSGCoTwoNativeTwentyTwoCaches02.R05p01_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches00.B3_data CFSGCoTwoNativeTwentyTwoCaches02.R05p01_data
    CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding CFSGCoTwoNativeTwentyTwoProducts00.cache_B3
    (by decide : 22*(2-1)^2<32) checks_R05p01

private theorem check_R05p02_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 0 j%2 := by decide +kernel

private theorem check_R05p02_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 1 j%2 := by decide +kernel

private theorem check_R05p02_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 2 j%2 := by decide +kernel

private theorem check_R05p02_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 3 j%2 := by decide +kernel

private theorem check_R05p02_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 4 j%2 := by decide +kernel

private theorem check_R05p02_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 5 j%2 := by decide +kernel

private theorem check_R05p02_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 6 j%2 := by decide +kernel

private theorem check_R05p02_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 7 j%2 := by decide +kernel

private theorem check_R05p02_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 8 j%2 := by decide +kernel

private theorem check_R05p02_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 9 j%2 := by decide +kernel

private theorem check_R05p02_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 10 j%2 := by decide +kernel

private theorem check_R05p02_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 11 j%2 := by decide +kernel

private theorem check_R05p02_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 12 j%2 := by decide +kernel

private theorem check_R05p02_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 13 j%2 := by decide +kernel

private theorem check_R05p02_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 14 j%2 := by decide +kernel

private theorem check_R05p02_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 15 j%2 := by decide +kernel

private theorem check_R05p02_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 16 j%2 := by decide +kernel

private theorem check_R05p02_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 17 j%2 := by decide +kernel

private theorem check_R05p02_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 18 j%2 := by decide +kernel

private theorem check_R05p02_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 19 j%2 := by decide +kernel

private theorem check_R05p02_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 20 j%2 := by decide +kernel

private theorem check_R05p02_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit 21 j%2 := by decide +kernel

theorem checks_R05p02 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p01_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R05p02_00 j
  · exact check_R05p02_01 j
  · exact check_R05p02_02 j
  · exact check_R05p02_03 j
  · exact check_R05p02_04 j
  · exact check_R05p02_05 j
  · exact check_R05p02_06 j
  · exact check_R05p02_07 j
  · exact check_R05p02_08 j
  · exact check_R05p02_09 j
  · exact check_R05p02_10 j
  · exact check_R05p02_11 j
  · exact check_R05p02_12 j
  · exact check_R05p02_13 j
  · exact check_R05p02_14 j
  · exact check_R05p02_15 j
  · exact check_R05p02_16 j
  · exact check_R05p02_17 j
  · exact check_R05p02_18 j
  · exact check_R05p02_19 j
  · exact check_R05p02_20 j
  · exact check_R05p02_21 j

def matrix_R05p02 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05p01)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_R05p02 : matrix_R05p02=CFSGCoTwoNativeTwentyTwoCaches02.R05p02_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches02.R05p01_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches02.R05p02_data
    CFSGCoTwoNativeTwentyTwoProducts01.cache_R05p01 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_R05p02

private theorem check_R05p03_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 0 j%2 := by decide +kernel

private theorem check_R05p03_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 1 j%2 := by decide +kernel

private theorem check_R05p03_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 2 j%2 := by decide +kernel

private theorem check_R05p03_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 3 j%2 := by decide +kernel

private theorem check_R05p03_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 4 j%2 := by decide +kernel

private theorem check_R05p03_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 5 j%2 := by decide +kernel

private theorem check_R05p03_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 6 j%2 := by decide +kernel

private theorem check_R05p03_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 7 j%2 := by decide +kernel

private theorem check_R05p03_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 8 j%2 := by decide +kernel

private theorem check_R05p03_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 9 j%2 := by decide +kernel

private theorem check_R05p03_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 10 j%2 := by decide +kernel

private theorem check_R05p03_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 11 j%2 := by decide +kernel

private theorem check_R05p03_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 12 j%2 := by decide +kernel

private theorem check_R05p03_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 13 j%2 := by decide +kernel

private theorem check_R05p03_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 14 j%2 := by decide +kernel

private theorem check_R05p03_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 15 j%2 := by decide +kernel

private theorem check_R05p03_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 16 j%2 := by decide +kernel

private theorem check_R05p03_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 17 j%2 := by decide +kernel

private theorem check_R05p03_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 18 j%2 := by decide +kernel

private theorem check_R05p03_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 19 j%2 := by decide +kernel

private theorem check_R05p03_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 20 j%2 := by decide +kernel

private theorem check_R05p03_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit 21 j%2 := by decide +kernel

theorem checks_R05p03 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p02_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R05p03_00 j
  · exact check_R05p03_01 j
  · exact check_R05p03_02 j
  · exact check_R05p03_03 j
  · exact check_R05p03_04 j
  · exact check_R05p03_05 j
  · exact check_R05p03_06 j
  · exact check_R05p03_07 j
  · exact check_R05p03_08 j
  · exact check_R05p03_09 j
  · exact check_R05p03_10 j
  · exact check_R05p03_11 j
  · exact check_R05p03_12 j
  · exact check_R05p03_13 j
  · exact check_R05p03_14 j
  · exact check_R05p03_15 j
  · exact check_R05p03_16 j
  · exact check_R05p03_17 j
  · exact check_R05p03_18 j
  · exact check_R05p03_19 j
  · exact check_R05p03_20 j
  · exact check_R05p03_21 j

def matrix_R05p03 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05p02)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)

theorem cache_R05p03 : matrix_R05p03=CFSGCoTwoNativeTwentyTwoCaches02.R05p03_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches02.R05p02_data CFSGCoTwoNativeTwentyTwoBaseCaches.B2_data CFSGCoTwoNativeTwentyTwoCaches02.R05p03_data
    CFSGCoTwoNativeTwentyTwoProducts01.cache_R05p02 CFSGCoTwoNativeTwentyTwoPowerPilot.cache_B2
    (by decide : 22*(2-1)^2<32) checks_R05p03

private theorem check_R05e02_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 0 j%2 := by decide +kernel

private theorem check_R05e02_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 1 j%2 := by decide +kernel

private theorem check_R05e02_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 2 j%2 := by decide +kernel

private theorem check_R05e02_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 3 j%2 := by decide +kernel

private theorem check_R05e02_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 4 j%2 := by decide +kernel

private theorem check_R05e02_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 5 j%2 := by decide +kernel

private theorem check_R05e02_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 6 j%2 := by decide +kernel

private theorem check_R05e02_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 7 j%2 := by decide +kernel

private theorem check_R05e02_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 8 j%2 := by decide +kernel

private theorem check_R05e02_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 9 j%2 := by decide +kernel

private theorem check_R05e02_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 10 j%2 := by decide +kernel

private theorem check_R05e02_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 11 j%2 := by decide +kernel

private theorem check_R05e02_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 12 j%2 := by decide +kernel

private theorem check_R05e02_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 13 j%2 := by decide +kernel

private theorem check_R05e02_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 14 j%2 := by decide +kernel

private theorem check_R05e02_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 15 j%2 := by decide +kernel

private theorem check_R05e02_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 16 j%2 := by decide +kernel

private theorem check_R05e02_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 17 j%2 := by decide +kernel

private theorem check_R05e02_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 18 j%2 := by decide +kernel

private theorem check_R05e02_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 19 j%2 := by decide +kernel

private theorem check_R05e02_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 20 j%2 := by decide +kernel

private theorem check_R05e02_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit 21 j%2 := by decide +kernel

theorem checks_R05e02 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches02.R05p03_rowCode i*CFSGCoTwoNativeTwentyTwoCaches02.R05p03_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R05e02_00 j
  · exact check_R05e02_01 j
  · exact check_R05e02_02 j
  · exact check_R05e02_03 j
  · exact check_R05e02_04 j
  · exact check_R05e02_05 j
  · exact check_R05e02_06 j
  · exact check_R05e02_07 j
  · exact check_R05e02_08 j
  · exact check_R05e02_09 j
  · exact check_R05e02_10 j
  · exact check_R05e02_11 j
  · exact check_R05e02_12 j
  · exact check_R05e02_13 j
  · exact check_R05e02_14 j
  · exact check_R05e02_15 j
  · exact check_R05e02_16 j
  · exact check_R05e02_17 j
  · exact check_R05e02_18 j
  · exact check_R05e02_19 j
  · exact check_R05e02_20 j
  · exact check_R05e02_21 j

def matrix_R05e02 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05p03)*(CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05p03)

theorem cache_R05e02 : matrix_R05e02=CFSGCoTwoNativeTwentyTwoCaches03.R05e02_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches02.R05p03_data CFSGCoTwoNativeTwentyTwoCaches02.R05p03_data CFSGCoTwoNativeTwentyTwoCaches03.R05e02_data
    CFSGCoTwoNativeTwentyTwoProducts01.cache_R05p03 CFSGCoTwoNativeTwentyTwoProducts01.cache_R05p03
    (by decide : 22*(2-1)^2<32) checks_R05e02

private theorem check_R05e04_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 0 j%2 := by decide +kernel

private theorem check_R05e04_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 1 j%2 := by decide +kernel

private theorem check_R05e04_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 2 j%2 := by decide +kernel

private theorem check_R05e04_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 3 j%2 := by decide +kernel

private theorem check_R05e04_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 4 j%2 := by decide +kernel

private theorem check_R05e04_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 5 j%2 := by decide +kernel

private theorem check_R05e04_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 6 j%2 := by decide +kernel

private theorem check_R05e04_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 7 j%2 := by decide +kernel

private theorem check_R05e04_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 8 j%2 := by decide +kernel

private theorem check_R05e04_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 9 j%2 := by decide +kernel

private theorem check_R05e04_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 10 j%2 := by decide +kernel

private theorem check_R05e04_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 11 j%2 := by decide +kernel

private theorem check_R05e04_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 12 j%2 := by decide +kernel

private theorem check_R05e04_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 13 j%2 := by decide +kernel

private theorem check_R05e04_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 14 j%2 := by decide +kernel

private theorem check_R05e04_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 15 j%2 := by decide +kernel

private theorem check_R05e04_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 16 j%2 := by decide +kernel

private theorem check_R05e04_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 17 j%2 := by decide +kernel

private theorem check_R05e04_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 18 j%2 := by decide +kernel

private theorem check_R05e04_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 19 j%2 := by decide +kernel

private theorem check_R05e04_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 20 j%2 := by decide +kernel

private theorem check_R05e04_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 21 j%2 := by decide +kernel

theorem checks_R05e04 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R05e02_rowCode i*CFSGCoTwoNativeTwentyTwoCaches03.R05e02_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R05e04_00 j
  · exact check_R05e04_01 j
  · exact check_R05e04_02 j
  · exact check_R05e04_03 j
  · exact check_R05e04_04 j
  · exact check_R05e04_05 j
  · exact check_R05e04_06 j
  · exact check_R05e04_07 j
  · exact check_R05e04_08 j
  · exact check_R05e04_09 j
  · exact check_R05e04_10 j
  · exact check_R05e04_11 j
  · exact check_R05e04_12 j
  · exact check_R05e04_13 j
  · exact check_R05e04_14 j
  · exact check_R05e04_15 j
  · exact check_R05e04_16 j
  · exact check_R05e04_17 j
  · exact check_R05e04_18 j
  · exact check_R05e04_19 j
  · exact check_R05e04_20 j
  · exact check_R05e04_21 j

def matrix_R05e04 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05e02)*(CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05e02)

theorem cache_R05e04 : matrix_R05e04=CFSGCoTwoNativeTwentyTwoBaseCaches.I_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches03.R05e02_data CFSGCoTwoNativeTwentyTwoCaches03.R05e02_data CFSGCoTwoNativeTwentyTwoBaseCaches.I_data
    CFSGCoTwoNativeTwentyTwoProducts01.cache_R05e02 CFSGCoTwoNativeTwentyTwoProducts01.cache_R05e02
    (by decide : 22*(2-1)^2<32) checks_R05e04

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts01
