import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches04
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoBaseCaches
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches05
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches06
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts02
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoPowerPilot
import Mathlib.Tactic.FinCases

/-! Fixed Co2 positive products; every whole matrix entry checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts03
open MatrixKroneckerProductReflection

private theorem check_R07p04_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 0 j%2 := by decide +kernel

private theorem check_R07p04_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 1 j%2 := by decide +kernel

private theorem check_R07p04_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 2 j%2 := by decide +kernel

private theorem check_R07p04_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 3 j%2 := by decide +kernel

private theorem check_R07p04_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 4 j%2 := by decide +kernel

private theorem check_R07p04_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 5 j%2 := by decide +kernel

private theorem check_R07p04_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 6 j%2 := by decide +kernel

private theorem check_R07p04_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 7 j%2 := by decide +kernel

private theorem check_R07p04_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 8 j%2 := by decide +kernel

private theorem check_R07p04_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 9 j%2 := by decide +kernel

private theorem check_R07p04_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 10 j%2 := by decide +kernel

private theorem check_R07p04_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 11 j%2 := by decide +kernel

private theorem check_R07p04_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 12 j%2 := by decide +kernel

private theorem check_R07p04_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 13 j%2 := by decide +kernel

private theorem check_R07p04_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 14 j%2 := by decide +kernel

private theorem check_R07p04_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 15 j%2 := by decide +kernel

private theorem check_R07p04_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 16 j%2 := by decide +kernel

private theorem check_R07p04_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 17 j%2 := by decide +kernel

private theorem check_R07p04_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 18 j%2 := by decide +kernel

private theorem check_R07p04_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 19 j%2 := by decide +kernel

private theorem check_R07p04_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 20 j%2 := by decide +kernel

private theorem check_R07p04_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit 21 j%2 := by decide +kernel

theorem checks_R07p04 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R07p03_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R07p04_00 j
  · exact check_R07p04_01 j
  · exact check_R07p04_02 j
  · exact check_R07p04_03 j
  · exact check_R07p04_04 j
  · exact check_R07p04_05 j
  · exact check_R07p04_06 j
  · exact check_R07p04_07 j
  · exact check_R07p04_08 j
  · exact check_R07p04_09 j
  · exact check_R07p04_10 j
  · exact check_R07p04_11 j
  · exact check_R07p04_12 j
  · exact check_R07p04_13 j
  · exact check_R07p04_14 j
  · exact check_R07p04_15 j
  · exact check_R07p04_16 j
  · exact check_R07p04_17 j
  · exact check_R07p04_18 j
  · exact check_R07p04_19 j
  · exact check_R07p04_20 j
  · exact check_R07p04_21 j

def matrix_R07p04 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts02.matrix_R07p03)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_R07p04 : matrix_R07p04=CFSGCoTwoNativeTwentyTwoCaches05.R07p04_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches04.R07p03_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches05.R07p04_data
    CFSGCoTwoNativeTwentyTwoProducts02.cache_R07p03 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_R07p04

private theorem check_R07p05_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 0 j%2 := by decide +kernel

private theorem check_R07p05_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 1 j%2 := by decide +kernel

private theorem check_R07p05_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 2 j%2 := by decide +kernel

private theorem check_R07p05_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 3 j%2 := by decide +kernel

private theorem check_R07p05_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 4 j%2 := by decide +kernel

private theorem check_R07p05_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 5 j%2 := by decide +kernel

private theorem check_R07p05_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 6 j%2 := by decide +kernel

private theorem check_R07p05_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 7 j%2 := by decide +kernel

private theorem check_R07p05_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 8 j%2 := by decide +kernel

private theorem check_R07p05_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 9 j%2 := by decide +kernel

private theorem check_R07p05_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 10 j%2 := by decide +kernel

private theorem check_R07p05_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 11 j%2 := by decide +kernel

private theorem check_R07p05_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 12 j%2 := by decide +kernel

private theorem check_R07p05_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 13 j%2 := by decide +kernel

private theorem check_R07p05_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 14 j%2 := by decide +kernel

private theorem check_R07p05_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 15 j%2 := by decide +kernel

private theorem check_R07p05_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 16 j%2 := by decide +kernel

private theorem check_R07p05_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 17 j%2 := by decide +kernel

private theorem check_R07p05_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 18 j%2 := by decide +kernel

private theorem check_R07p05_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 19 j%2 := by decide +kernel

private theorem check_R07p05_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 20 j%2 := by decide +kernel

private theorem check_R07p05_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit 21 j%2 := by decide +kernel

theorem checks_R07p05 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p04_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R07p05_00 j
  · exact check_R07p05_01 j
  · exact check_R07p05_02 j
  · exact check_R07p05_03 j
  · exact check_R07p05_04 j
  · exact check_R07p05_05 j
  · exact check_R07p05_06 j
  · exact check_R07p05_07 j
  · exact check_R07p05_08 j
  · exact check_R07p05_09 j
  · exact check_R07p05_10 j
  · exact check_R07p05_11 j
  · exact check_R07p05_12 j
  · exact check_R07p05_13 j
  · exact check_R07p05_14 j
  · exact check_R07p05_15 j
  · exact check_R07p05_16 j
  · exact check_R07p05_17 j
  · exact check_R07p05_18 j
  · exact check_R07p05_19 j
  · exact check_R07p05_20 j
  · exact check_R07p05_21 j

def matrix_R07p05 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p04)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B4)

theorem cache_R07p05 : matrix_R07p05=CFSGCoTwoNativeTwentyTwoCaches05.R07p05_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches05.R07p04_data CFSGCoTwoNativeTwentyTwoBaseCaches.B4_data CFSGCoTwoNativeTwentyTwoCaches05.R07p05_data
    CFSGCoTwoNativeTwentyTwoProducts03.cache_R07p04 CFSGCoTwoNativeTwentyTwoPowerPilot.cache_B4
    (by decide : 22*(2-1)^2<32) checks_R07p05

private theorem check_R07p06_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 0 j%2 := by decide +kernel

private theorem check_R07p06_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 1 j%2 := by decide +kernel

private theorem check_R07p06_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 2 j%2 := by decide +kernel

private theorem check_R07p06_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 3 j%2 := by decide +kernel

private theorem check_R07p06_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 4 j%2 := by decide +kernel

private theorem check_R07p06_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 5 j%2 := by decide +kernel

private theorem check_R07p06_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 6 j%2 := by decide +kernel

private theorem check_R07p06_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 7 j%2 := by decide +kernel

private theorem check_R07p06_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 8 j%2 := by decide +kernel

private theorem check_R07p06_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 9 j%2 := by decide +kernel

private theorem check_R07p06_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 10 j%2 := by decide +kernel

private theorem check_R07p06_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 11 j%2 := by decide +kernel

private theorem check_R07p06_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 12 j%2 := by decide +kernel

private theorem check_R07p06_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 13 j%2 := by decide +kernel

private theorem check_R07p06_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 14 j%2 := by decide +kernel

private theorem check_R07p06_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 15 j%2 := by decide +kernel

private theorem check_R07p06_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 16 j%2 := by decide +kernel

private theorem check_R07p06_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 17 j%2 := by decide +kernel

private theorem check_R07p06_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 18 j%2 := by decide +kernel

private theorem check_R07p06_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 19 j%2 := by decide +kernel

private theorem check_R07p06_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 20 j%2 := by decide +kernel

private theorem check_R07p06_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit 21 j%2 := by decide +kernel

theorem checks_R07p06 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p05_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R07p06_00 j
  · exact check_R07p06_01 j
  · exact check_R07p06_02 j
  · exact check_R07p06_03 j
  · exact check_R07p06_04 j
  · exact check_R07p06_05 j
  · exact check_R07p06_06 j
  · exact check_R07p06_07 j
  · exact check_R07p06_08 j
  · exact check_R07p06_09 j
  · exact check_R07p06_10 j
  · exact check_R07p06_11 j
  · exact check_R07p06_12 j
  · exact check_R07p06_13 j
  · exact check_R07p06_14 j
  · exact check_R07p06_15 j
  · exact check_R07p06_16 j
  · exact check_R07p06_17 j
  · exact check_R07p06_18 j
  · exact check_R07p06_19 j
  · exact check_R07p06_20 j
  · exact check_R07p06_21 j

def matrix_R07p06 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p05)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_R07p06 : matrix_R07p06=CFSGCoTwoNativeTwentyTwoCaches05.R07p06_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches05.R07p05_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches05.R07p06_data
    CFSGCoTwoNativeTwentyTwoProducts03.cache_R07p05 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_R07p06

private theorem check_R07p07_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 0 j%2 := by decide +kernel

private theorem check_R07p07_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 1 j%2 := by decide +kernel

private theorem check_R07p07_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 2 j%2 := by decide +kernel

private theorem check_R07p07_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 3 j%2 := by decide +kernel

private theorem check_R07p07_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 4 j%2 := by decide +kernel

private theorem check_R07p07_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 5 j%2 := by decide +kernel

private theorem check_R07p07_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 6 j%2 := by decide +kernel

private theorem check_R07p07_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 7 j%2 := by decide +kernel

private theorem check_R07p07_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 8 j%2 := by decide +kernel

private theorem check_R07p07_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 9 j%2 := by decide +kernel

private theorem check_R07p07_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 10 j%2 := by decide +kernel

private theorem check_R07p07_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 11 j%2 := by decide +kernel

private theorem check_R07p07_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 12 j%2 := by decide +kernel

private theorem check_R07p07_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 13 j%2 := by decide +kernel

private theorem check_R07p07_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 14 j%2 := by decide +kernel

private theorem check_R07p07_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 15 j%2 := by decide +kernel

private theorem check_R07p07_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 16 j%2 := by decide +kernel

private theorem check_R07p07_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 17 j%2 := by decide +kernel

private theorem check_R07p07_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 18 j%2 := by decide +kernel

private theorem check_R07p07_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 19 j%2 := by decide +kernel

private theorem check_R07p07_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 20 j%2 := by decide +kernel

private theorem check_R07p07_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit 21 j%2 := by decide +kernel

theorem checks_R07p07 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p06_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R07p07_00 j
  · exact check_R07p07_01 j
  · exact check_R07p07_02 j
  · exact check_R07p07_03 j
  · exact check_R07p07_04 j
  · exact check_R07p07_05 j
  · exact check_R07p07_06 j
  · exact check_R07p07_07 j
  · exact check_R07p07_08 j
  · exact check_R07p07_09 j
  · exact check_R07p07_10 j
  · exact check_R07p07_11 j
  · exact check_R07p07_12 j
  · exact check_R07p07_13 j
  · exact check_R07p07_14 j
  · exact check_R07p07_15 j
  · exact check_R07p07_16 j
  · exact check_R07p07_17 j
  · exact check_R07p07_18 j
  · exact check_R07p07_19 j
  · exact check_R07p07_20 j
  · exact check_R07p07_21 j

def matrix_R07p07 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p06)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixB)

theorem cache_R07p07 : matrix_R07p07=CFSGCoTwoNativeTwentyTwoCaches05.R07p07_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches05.R07p06_data CFSGCoTwoNativeTwentyTwoBaseCaches.B_data CFSGCoTwoNativeTwentyTwoCaches05.R07p07_data
    CFSGCoTwoNativeTwentyTwoProducts03.cache_R07p06 CFSGCoTwoNativeTwentyTwoBaseCaches.B_source_binding
    (by decide : 22*(2-1)^2<32) checks_R07p07

private theorem check_R07p08_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 0 j%2 := by decide +kernel

private theorem check_R07p08_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 1 j%2 := by decide +kernel

private theorem check_R07p08_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 2 j%2 := by decide +kernel

private theorem check_R07p08_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 3 j%2 := by decide +kernel

private theorem check_R07p08_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 4 j%2 := by decide +kernel

private theorem check_R07p08_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 5 j%2 := by decide +kernel

private theorem check_R07p08_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 6 j%2 := by decide +kernel

private theorem check_R07p08_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 7 j%2 := by decide +kernel

private theorem check_R07p08_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 8 j%2 := by decide +kernel

private theorem check_R07p08_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 9 j%2 := by decide +kernel

private theorem check_R07p08_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 10 j%2 := by decide +kernel

private theorem check_R07p08_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 11 j%2 := by decide +kernel

private theorem check_R07p08_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 12 j%2 := by decide +kernel

private theorem check_R07p08_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 13 j%2 := by decide +kernel

private theorem check_R07p08_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 14 j%2 := by decide +kernel

private theorem check_R07p08_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 15 j%2 := by decide +kernel

private theorem check_R07p08_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 16 j%2 := by decide +kernel

private theorem check_R07p08_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 17 j%2 := by decide +kernel

private theorem check_R07p08_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 18 j%2 := by decide +kernel

private theorem check_R07p08_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 19 j%2 := by decide +kernel

private theorem check_R07p08_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 20 j%2 := by decide +kernel

private theorem check_R07p08_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit 21 j%2 := by decide +kernel

theorem checks_R07p08 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches05.R07p07_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R07p08_00 j
  · exact check_R07p08_01 j
  · exact check_R07p08_02 j
  · exact check_R07p08_03 j
  · exact check_R07p08_04 j
  · exact check_R07p08_05 j
  · exact check_R07p08_06 j
  · exact check_R07p08_07 j
  · exact check_R07p08_08 j
  · exact check_R07p08_09 j
  · exact check_R07p08_10 j
  · exact check_R07p08_11 j
  · exact check_R07p08_12 j
  · exact check_R07p08_13 j
  · exact check_R07p08_14 j
  · exact check_R07p08_15 j
  · exact check_R07p08_16 j
  · exact check_R07p08_17 j
  · exact check_R07p08_18 j
  · exact check_R07p08_19 j
  · exact check_R07p08_20 j
  · exact check_R07p08_21 j

def matrix_R07p08 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p07)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_R07p08 : matrix_R07p08=CFSGCoTwoNativeTwentyTwoCaches06.R07p08_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches05.R07p07_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches06.R07p08_data
    CFSGCoTwoNativeTwentyTwoProducts03.cache_R07p07 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_R07p08

private theorem check_R07p09_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 0 j%2 := by decide +kernel

private theorem check_R07p09_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 1 j%2 := by decide +kernel

private theorem check_R07p09_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 2 j%2 := by decide +kernel

private theorem check_R07p09_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 3 j%2 := by decide +kernel

private theorem check_R07p09_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 4 j%2 := by decide +kernel

private theorem check_R07p09_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 5 j%2 := by decide +kernel

private theorem check_R07p09_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 6 j%2 := by decide +kernel

private theorem check_R07p09_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 7 j%2 := by decide +kernel

private theorem check_R07p09_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 8 j%2 := by decide +kernel

private theorem check_R07p09_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 9 j%2 := by decide +kernel

private theorem check_R07p09_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 10 j%2 := by decide +kernel

private theorem check_R07p09_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 11 j%2 := by decide +kernel

private theorem check_R07p09_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 12 j%2 := by decide +kernel

private theorem check_R07p09_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 13 j%2 := by decide +kernel

private theorem check_R07p09_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 14 j%2 := by decide +kernel

private theorem check_R07p09_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 15 j%2 := by decide +kernel

private theorem check_R07p09_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 16 j%2 := by decide +kernel

private theorem check_R07p09_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 17 j%2 := by decide +kernel

private theorem check_R07p09_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 18 j%2 := by decide +kernel

private theorem check_R07p09_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 19 j%2 := by decide +kernel

private theorem check_R07p09_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 20 j%2 := by decide +kernel

private theorem check_R07p09_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit 21 j%2 := by decide +kernel

theorem checks_R07p09 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p08_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R07p09_00 j
  · exact check_R07p09_01 j
  · exact check_R07p09_02 j
  · exact check_R07p09_03 j
  · exact check_R07p09_04 j
  · exact check_R07p09_05 j
  · exact check_R07p09_06 j
  · exact check_R07p09_07 j
  · exact check_R07p09_08 j
  · exact check_R07p09_09 j
  · exact check_R07p09_10 j
  · exact check_R07p09_11 j
  · exact check_R07p09_12 j
  · exact check_R07p09_13 j
  · exact check_R07p09_14 j
  · exact check_R07p09_15 j
  · exact check_R07p09_16 j
  · exact check_R07p09_17 j
  · exact check_R07p09_18 j
  · exact check_R07p09_19 j
  · exact check_R07p09_20 j
  · exact check_R07p09_21 j

def matrix_R07p09 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p08)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)

theorem cache_R07p09 : matrix_R07p09=CFSGCoTwoNativeTwentyTwoCaches06.R07p09_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches06.R07p08_data CFSGCoTwoNativeTwentyTwoBaseCaches.B2_data CFSGCoTwoNativeTwentyTwoCaches06.R07p09_data
    CFSGCoTwoNativeTwentyTwoProducts03.cache_R07p08 CFSGCoTwoNativeTwentyTwoPowerPilot.cache_B2
    (by decide : 22*(2-1)^2<32) checks_R07p09

private theorem check_R07p10_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 0 j%2 := by decide +kernel

private theorem check_R07p10_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 1 j%2 := by decide +kernel

private theorem check_R07p10_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 2 j%2 := by decide +kernel

private theorem check_R07p10_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 3 j%2 := by decide +kernel

private theorem check_R07p10_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 4 j%2 := by decide +kernel

private theorem check_R07p10_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 5 j%2 := by decide +kernel

private theorem check_R07p10_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 6 j%2 := by decide +kernel

private theorem check_R07p10_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 7 j%2 := by decide +kernel

private theorem check_R07p10_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 8 j%2 := by decide +kernel

private theorem check_R07p10_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 9 j%2 := by decide +kernel

private theorem check_R07p10_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 10 j%2 := by decide +kernel

private theorem check_R07p10_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 11 j%2 := by decide +kernel

private theorem check_R07p10_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 12 j%2 := by decide +kernel

private theorem check_R07p10_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 13 j%2 := by decide +kernel

private theorem check_R07p10_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 14 j%2 := by decide +kernel

private theorem check_R07p10_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 15 j%2 := by decide +kernel

private theorem check_R07p10_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 16 j%2 := by decide +kernel

private theorem check_R07p10_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 17 j%2 := by decide +kernel

private theorem check_R07p10_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 18 j%2 := by decide +kernel

private theorem check_R07p10_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 19 j%2 := by decide +kernel

private theorem check_R07p10_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 20 j%2 := by decide +kernel

private theorem check_R07p10_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit 21 j%2 := by decide +kernel

theorem checks_R07p10 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p09_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R07p10_00 j
  · exact check_R07p10_01 j
  · exact check_R07p10_02 j
  · exact check_R07p10_03 j
  · exact check_R07p10_04 j
  · exact check_R07p10_05 j
  · exact check_R07p10_06 j
  · exact check_R07p10_07 j
  · exact check_R07p10_08 j
  · exact check_R07p10_09 j
  · exact check_R07p10_10 j
  · exact check_R07p10_11 j
  · exact check_R07p10_12 j
  · exact check_R07p10_13 j
  · exact check_R07p10_14 j
  · exact check_R07p10_15 j
  · exact check_R07p10_16 j
  · exact check_R07p10_17 j
  · exact check_R07p10_18 j
  · exact check_R07p10_19 j
  · exact check_R07p10_20 j
  · exact check_R07p10_21 j

def matrix_R07p10 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p09)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_R07p10 : matrix_R07p10=CFSGCoTwoNativeTwentyTwoCaches06.R07p10_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches06.R07p09_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches06.R07p10_data
    CFSGCoTwoNativeTwentyTwoProducts03.cache_R07p09 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_R07p10

private theorem check_R07p11_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 0 j%2 := by decide +kernel

private theorem check_R07p11_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 1 j%2 := by decide +kernel

private theorem check_R07p11_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 2 j%2 := by decide +kernel

private theorem check_R07p11_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 3 j%2 := by decide +kernel

private theorem check_R07p11_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 4 j%2 := by decide +kernel

private theorem check_R07p11_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 5 j%2 := by decide +kernel

private theorem check_R07p11_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 6 j%2 := by decide +kernel

private theorem check_R07p11_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 7 j%2 := by decide +kernel

private theorem check_R07p11_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 8 j%2 := by decide +kernel

private theorem check_R07p11_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 9 j%2 := by decide +kernel

private theorem check_R07p11_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 10 j%2 := by decide +kernel

private theorem check_R07p11_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 11 j%2 := by decide +kernel

private theorem check_R07p11_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 12 j%2 := by decide +kernel

private theorem check_R07p11_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 13 j%2 := by decide +kernel

private theorem check_R07p11_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 14 j%2 := by decide +kernel

private theorem check_R07p11_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 15 j%2 := by decide +kernel

private theorem check_R07p11_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 16 j%2 := by decide +kernel

private theorem check_R07p11_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 17 j%2 := by decide +kernel

private theorem check_R07p11_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 18 j%2 := by decide +kernel

private theorem check_R07p11_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 19 j%2 := by decide +kernel

private theorem check_R07p11_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 20 j%2 := by decide +kernel

private theorem check_R07p11_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit 21 j%2 := by decide +kernel

theorem checks_R07p11 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p10_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R07p11_00 j
  · exact check_R07p11_01 j
  · exact check_R07p11_02 j
  · exact check_R07p11_03 j
  · exact check_R07p11_04 j
  · exact check_R07p11_05 j
  · exact check_R07p11_06 j
  · exact check_R07p11_07 j
  · exact check_R07p11_08 j
  · exact check_R07p11_09 j
  · exact check_R07p11_10 j
  · exact check_R07p11_11 j
  · exact check_R07p11_12 j
  · exact check_R07p11_13 j
  · exact check_R07p11_14 j
  · exact check_R07p11_15 j
  · exact check_R07p11_16 j
  · exact check_R07p11_17 j
  · exact check_R07p11_18 j
  · exact check_R07p11_19 j
  · exact check_R07p11_20 j
  · exact check_R07p11_21 j

def matrix_R07p11 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p10)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixB)

theorem cache_R07p11 : matrix_R07p11=CFSGCoTwoNativeTwentyTwoCaches06.R07p11_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches06.R07p10_data CFSGCoTwoNativeTwentyTwoBaseCaches.B_data CFSGCoTwoNativeTwentyTwoCaches06.R07p11_data
    CFSGCoTwoNativeTwentyTwoProducts03.cache_R07p10 CFSGCoTwoNativeTwentyTwoBaseCaches.B_source_binding
    (by decide : 22*(2-1)^2<32) checks_R07p11

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts03
