import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches08
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoBaseCaches
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches07
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches09
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches00
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches10
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts04
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoPowerPilot
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts00
import Mathlib.Tactic.FinCases

/-! Fixed Co2 positive products; every whole matrix entry checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts05
open MatrixKroneckerProductReflection

private theorem check_R08e03_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 0 j%2 := by decide +kernel

private theorem check_R08e03_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 1 j%2 := by decide +kernel

private theorem check_R08e03_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 2 j%2 := by decide +kernel

private theorem check_R08e03_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 3 j%2 := by decide +kernel

private theorem check_R08e03_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 4 j%2 := by decide +kernel

private theorem check_R08e03_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 5 j%2 := by decide +kernel

private theorem check_R08e03_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 6 j%2 := by decide +kernel

private theorem check_R08e03_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 7 j%2 := by decide +kernel

private theorem check_R08e03_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 8 j%2 := by decide +kernel

private theorem check_R08e03_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 9 j%2 := by decide +kernel

private theorem check_R08e03_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 10 j%2 := by decide +kernel

private theorem check_R08e03_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 11 j%2 := by decide +kernel

private theorem check_R08e03_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 12 j%2 := by decide +kernel

private theorem check_R08e03_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 13 j%2 := by decide +kernel

private theorem check_R08e03_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 14 j%2 := by decide +kernel

private theorem check_R08e03_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 15 j%2 := by decide +kernel

private theorem check_R08e03_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 16 j%2 := by decide +kernel

private theorem check_R08e03_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 17 j%2 := by decide +kernel

private theorem check_R08e03_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 18 j%2 := by decide +kernel

private theorem check_R08e03_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 19 j%2 := by decide +kernel

private theorem check_R08e03_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 20 j%2 := by decide +kernel

private theorem check_R08e03_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 21 j%2 := by decide +kernel

theorem checks_R08e03 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08e02_rowCode i*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R08e03_00 j
  · exact check_R08e03_01 j
  · exact check_R08e03_02 j
  · exact check_R08e03_03 j
  · exact check_R08e03_04 j
  · exact check_R08e03_05 j
  · exact check_R08e03_06 j
  · exact check_R08e03_07 j
  · exact check_R08e03_08 j
  · exact check_R08e03_09 j
  · exact check_R08e03_10 j
  · exact check_R08e03_11 j
  · exact check_R08e03_12 j
  · exact check_R08e03_13 j
  · exact check_R08e03_14 j
  · exact check_R08e03_15 j
  · exact check_R08e03_16 j
  · exact check_R08e03_17 j
  · exact check_R08e03_18 j
  · exact check_R08e03_19 j
  · exact check_R08e03_20 j
  · exact check_R08e03_21 j

def matrix_R08e03 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08e02)*(CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p07)

theorem cache_R08e03 : matrix_R08e03=CFSGCoTwoNativeTwentyTwoBaseCaches.I_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches08.R08e02_data CFSGCoTwoNativeTwentyTwoCaches08.R08p07_data CFSGCoTwoNativeTwentyTwoBaseCaches.I_data
    CFSGCoTwoNativeTwentyTwoProducts04.cache_R08e02 CFSGCoTwoNativeTwentyTwoProducts04.cache_R08p07
    (by decide : 22*(2-1)^2<32) checks_R08e03

private theorem check_R09p05_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 0 j%2 := by decide +kernel

private theorem check_R09p05_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 1 j%2 := by decide +kernel

private theorem check_R09p05_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 2 j%2 := by decide +kernel

private theorem check_R09p05_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 3 j%2 := by decide +kernel

private theorem check_R09p05_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 4 j%2 := by decide +kernel

private theorem check_R09p05_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 5 j%2 := by decide +kernel

private theorem check_R09p05_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 6 j%2 := by decide +kernel

private theorem check_R09p05_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 7 j%2 := by decide +kernel

private theorem check_R09p05_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 8 j%2 := by decide +kernel

private theorem check_R09p05_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 9 j%2 := by decide +kernel

private theorem check_R09p05_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 10 j%2 := by decide +kernel

private theorem check_R09p05_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 11 j%2 := by decide +kernel

private theorem check_R09p05_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 12 j%2 := by decide +kernel

private theorem check_R09p05_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 13 j%2 := by decide +kernel

private theorem check_R09p05_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 14 j%2 := by decide +kernel

private theorem check_R09p05_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 15 j%2 := by decide +kernel

private theorem check_R09p05_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 16 j%2 := by decide +kernel

private theorem check_R09p05_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 17 j%2 := by decide +kernel

private theorem check_R09p05_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 18 j%2 := by decide +kernel

private theorem check_R09p05_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 19 j%2 := by decide +kernel

private theorem check_R09p05_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 20 j%2 := by decide +kernel

private theorem check_R09p05_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit 21 j%2 := by decide +kernel

theorem checks_R09p05 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B2_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R09p05_00 j
  · exact check_R09p05_01 j
  · exact check_R09p05_02 j
  · exact check_R09p05_03 j
  · exact check_R09p05_04 j
  · exact check_R09p05_05 j
  · exact check_R09p05_06 j
  · exact check_R09p05_07 j
  · exact check_R09p05_08 j
  · exact check_R09p05_09 j
  · exact check_R09p05_10 j
  · exact check_R09p05_11 j
  · exact check_R09p05_12 j
  · exact check_R09p05_13 j
  · exact check_R09p05_14 j
  · exact check_R09p05_15 j
  · exact check_R09p05_16 j
  · exact check_R09p05_17 j
  · exact check_R09p05_18 j
  · exact check_R09p05_19 j
  · exact check_R09p05_20 j
  · exact check_R09p05_21 j

def matrix_R09p05 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p04)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)

theorem cache_R09p05 : matrix_R09p05=CFSGCoTwoNativeTwentyTwoCaches08.R09p05_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches07.R08p04_data CFSGCoTwoNativeTwentyTwoBaseCaches.B2_data CFSGCoTwoNativeTwentyTwoCaches08.R09p05_data
    CFSGCoTwoNativeTwentyTwoProducts04.cache_R08p04 CFSGCoTwoNativeTwentyTwoPowerPilot.cache_B2
    (by decide : 22*(2-1)^2<32) checks_R09p05

private theorem check_R09p06_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 0 j%2 := by decide +kernel

private theorem check_R09p06_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 1 j%2 := by decide +kernel

private theorem check_R09p06_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 2 j%2 := by decide +kernel

private theorem check_R09p06_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 3 j%2 := by decide +kernel

private theorem check_R09p06_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 4 j%2 := by decide +kernel

private theorem check_R09p06_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 5 j%2 := by decide +kernel

private theorem check_R09p06_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 6 j%2 := by decide +kernel

private theorem check_R09p06_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 7 j%2 := by decide +kernel

private theorem check_R09p06_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 8 j%2 := by decide +kernel

private theorem check_R09p06_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 9 j%2 := by decide +kernel

private theorem check_R09p06_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 10 j%2 := by decide +kernel

private theorem check_R09p06_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 11 j%2 := by decide +kernel

private theorem check_R09p06_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 12 j%2 := by decide +kernel

private theorem check_R09p06_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 13 j%2 := by decide +kernel

private theorem check_R09p06_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 14 j%2 := by decide +kernel

private theorem check_R09p06_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 15 j%2 := by decide +kernel

private theorem check_R09p06_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 16 j%2 := by decide +kernel

private theorem check_R09p06_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 17 j%2 := by decide +kernel

private theorem check_R09p06_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 18 j%2 := by decide +kernel

private theorem check_R09p06_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 19 j%2 := by decide +kernel

private theorem check_R09p06_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 20 j%2 := by decide +kernel

private theorem check_R09p06_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit 21 j%2 := by decide +kernel

theorem checks_R09p06 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R09p05_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R09p06_00 j
  · exact check_R09p06_01 j
  · exact check_R09p06_02 j
  · exact check_R09p06_03 j
  · exact check_R09p06_04 j
  · exact check_R09p06_05 j
  · exact check_R09p06_06 j
  · exact check_R09p06_07 j
  · exact check_R09p06_08 j
  · exact check_R09p06_09 j
  · exact check_R09p06_10 j
  · exact check_R09p06_11 j
  · exact check_R09p06_12 j
  · exact check_R09p06_13 j
  · exact check_R09p06_14 j
  · exact check_R09p06_15 j
  · exact check_R09p06_16 j
  · exact check_R09p06_17 j
  · exact check_R09p06_18 j
  · exact check_R09p06_19 j
  · exact check_R09p06_20 j
  · exact check_R09p06_21 j

def matrix_R09p06 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p05)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_R09p06 : matrix_R09p06=CFSGCoTwoNativeTwentyTwoCaches09.R09p06_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches08.R09p05_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches09.R09p06_data
    CFSGCoTwoNativeTwentyTwoProducts05.cache_R09p05 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_R09p06

private theorem check_R09p07_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 0 j%2 := by decide +kernel

private theorem check_R09p07_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 1 j%2 := by decide +kernel

private theorem check_R09p07_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 2 j%2 := by decide +kernel

private theorem check_R09p07_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 3 j%2 := by decide +kernel

private theorem check_R09p07_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 4 j%2 := by decide +kernel

private theorem check_R09p07_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 5 j%2 := by decide +kernel

private theorem check_R09p07_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 6 j%2 := by decide +kernel

private theorem check_R09p07_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 7 j%2 := by decide +kernel

private theorem check_R09p07_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 8 j%2 := by decide +kernel

private theorem check_R09p07_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 9 j%2 := by decide +kernel

private theorem check_R09p07_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 10 j%2 := by decide +kernel

private theorem check_R09p07_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 11 j%2 := by decide +kernel

private theorem check_R09p07_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 12 j%2 := by decide +kernel

private theorem check_R09p07_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 13 j%2 := by decide +kernel

private theorem check_R09p07_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 14 j%2 := by decide +kernel

private theorem check_R09p07_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 15 j%2 := by decide +kernel

private theorem check_R09p07_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 16 j%2 := by decide +kernel

private theorem check_R09p07_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 17 j%2 := by decide +kernel

private theorem check_R09p07_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 18 j%2 := by decide +kernel

private theorem check_R09p07_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 19 j%2 := by decide +kernel

private theorem check_R09p07_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 20 j%2 := by decide +kernel

private theorem check_R09p07_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit 21 j%2 := by decide +kernel

theorem checks_R09p07 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p06_rowCode i*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R09p07_00 j
  · exact check_R09p07_01 j
  · exact check_R09p07_02 j
  · exact check_R09p07_03 j
  · exact check_R09p07_04 j
  · exact check_R09p07_05 j
  · exact check_R09p07_06 j
  · exact check_R09p07_07 j
  · exact check_R09p07_08 j
  · exact check_R09p07_09 j
  · exact check_R09p07_10 j
  · exact check_R09p07_11 j
  · exact check_R09p07_12 j
  · exact check_R09p07_13 j
  · exact check_R09p07_14 j
  · exact check_R09p07_15 j
  · exact check_R09p07_16 j
  · exact check_R09p07_17 j
  · exact check_R09p07_18 j
  · exact check_R09p07_19 j
  · exact check_R09p07_20 j
  · exact check_R09p07_21 j

def matrix_R09p07 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p06)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_B3)

theorem cache_R09p07 : matrix_R09p07=CFSGCoTwoNativeTwentyTwoCaches09.R09p07_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches09.R09p06_data CFSGCoTwoNativeTwentyTwoCaches00.B3_data CFSGCoTwoNativeTwentyTwoCaches09.R09p07_data
    CFSGCoTwoNativeTwentyTwoProducts05.cache_R09p06 CFSGCoTwoNativeTwentyTwoProducts00.cache_B3
    (by decide : 22*(2-1)^2<32) checks_R09p07

private theorem check_R09p08_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 0 j%2 := by decide +kernel

private theorem check_R09p08_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 1 j%2 := by decide +kernel

private theorem check_R09p08_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 2 j%2 := by decide +kernel

private theorem check_R09p08_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 3 j%2 := by decide +kernel

private theorem check_R09p08_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 4 j%2 := by decide +kernel

private theorem check_R09p08_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 5 j%2 := by decide +kernel

private theorem check_R09p08_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 6 j%2 := by decide +kernel

private theorem check_R09p08_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 7 j%2 := by decide +kernel

private theorem check_R09p08_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 8 j%2 := by decide +kernel

private theorem check_R09p08_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 9 j%2 := by decide +kernel

private theorem check_R09p08_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 10 j%2 := by decide +kernel

private theorem check_R09p08_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 11 j%2 := by decide +kernel

private theorem check_R09p08_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 12 j%2 := by decide +kernel

private theorem check_R09p08_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 13 j%2 := by decide +kernel

private theorem check_R09p08_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 14 j%2 := by decide +kernel

private theorem check_R09p08_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 15 j%2 := by decide +kernel

private theorem check_R09p08_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 16 j%2 := by decide +kernel

private theorem check_R09p08_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 17 j%2 := by decide +kernel

private theorem check_R09p08_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 18 j%2 := by decide +kernel

private theorem check_R09p08_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 19 j%2 := by decide +kernel

private theorem check_R09p08_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 20 j%2 := by decide +kernel

private theorem check_R09p08_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit 21 j%2 := by decide +kernel

theorem checks_R09p08 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p07_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R09p08_00 j
  · exact check_R09p08_01 j
  · exact check_R09p08_02 j
  · exact check_R09p08_03 j
  · exact check_R09p08_04 j
  · exact check_R09p08_05 j
  · exact check_R09p08_06 j
  · exact check_R09p08_07 j
  · exact check_R09p08_08 j
  · exact check_R09p08_09 j
  · exact check_R09p08_10 j
  · exact check_R09p08_11 j
  · exact check_R09p08_12 j
  · exact check_R09p08_13 j
  · exact check_R09p08_14 j
  · exact check_R09p08_15 j
  · exact check_R09p08_16 j
  · exact check_R09p08_17 j
  · exact check_R09p08_18 j
  · exact check_R09p08_19 j
  · exact check_R09p08_20 j
  · exact check_R09p08_21 j

def matrix_R09p08 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p07)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_R09p08 : matrix_R09p08=CFSGCoTwoNativeTwentyTwoCaches09.R09p08_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches09.R09p07_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches09.R09p08_data
    CFSGCoTwoNativeTwentyTwoProducts05.cache_R09p07 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_R09p08

private theorem check_R09p09_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 0 j%2 := by decide +kernel

private theorem check_R09p09_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 1 j%2 := by decide +kernel

private theorem check_R09p09_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 2 j%2 := by decide +kernel

private theorem check_R09p09_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 3 j%2 := by decide +kernel

private theorem check_R09p09_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 4 j%2 := by decide +kernel

private theorem check_R09p09_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 5 j%2 := by decide +kernel

private theorem check_R09p09_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 6 j%2 := by decide +kernel

private theorem check_R09p09_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 7 j%2 := by decide +kernel

private theorem check_R09p09_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 8 j%2 := by decide +kernel

private theorem check_R09p09_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 9 j%2 := by decide +kernel

private theorem check_R09p09_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 10 j%2 := by decide +kernel

private theorem check_R09p09_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 11 j%2 := by decide +kernel

private theorem check_R09p09_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 12 j%2 := by decide +kernel

private theorem check_R09p09_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 13 j%2 := by decide +kernel

private theorem check_R09p09_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 14 j%2 := by decide +kernel

private theorem check_R09p09_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 15 j%2 := by decide +kernel

private theorem check_R09p09_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 16 j%2 := by decide +kernel

private theorem check_R09p09_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 17 j%2 := by decide +kernel

private theorem check_R09p09_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 18 j%2 := by decide +kernel

private theorem check_R09p09_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 19 j%2 := by decide +kernel

private theorem check_R09p09_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 20 j%2 := by decide +kernel

private theorem check_R09p09_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit 21 j%2 := by decide +kernel

theorem checks_R09p09 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p08_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R09p09_00 j
  · exact check_R09p09_01 j
  · exact check_R09p09_02 j
  · exact check_R09p09_03 j
  · exact check_R09p09_04 j
  · exact check_R09p09_05 j
  · exact check_R09p09_06 j
  · exact check_R09p09_07 j
  · exact check_R09p09_08 j
  · exact check_R09p09_09 j
  · exact check_R09p09_10 j
  · exact check_R09p09_11 j
  · exact check_R09p09_12 j
  · exact check_R09p09_13 j
  · exact check_R09p09_14 j
  · exact check_R09p09_15 j
  · exact check_R09p09_16 j
  · exact check_R09p09_17 j
  · exact check_R09p09_18 j
  · exact check_R09p09_19 j
  · exact check_R09p09_20 j
  · exact check_R09p09_21 j

def matrix_R09p09 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p08)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixB)

theorem cache_R09p09 : matrix_R09p09=CFSGCoTwoNativeTwentyTwoCaches09.R09p09_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches09.R09p08_data CFSGCoTwoNativeTwentyTwoBaseCaches.B_data CFSGCoTwoNativeTwentyTwoCaches09.R09p09_data
    CFSGCoTwoNativeTwentyTwoProducts05.cache_R09p08 CFSGCoTwoNativeTwentyTwoBaseCaches.B_source_binding
    (by decide : 22*(2-1)^2<32) checks_R09p09

private theorem check_R09p10_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 0 j%2 := by decide +kernel

private theorem check_R09p10_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 1 j%2 := by decide +kernel

private theorem check_R09p10_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 2 j%2 := by decide +kernel

private theorem check_R09p10_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 3 j%2 := by decide +kernel

private theorem check_R09p10_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 4 j%2 := by decide +kernel

private theorem check_R09p10_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 5 j%2 := by decide +kernel

private theorem check_R09p10_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 6 j%2 := by decide +kernel

private theorem check_R09p10_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 7 j%2 := by decide +kernel

private theorem check_R09p10_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 8 j%2 := by decide +kernel

private theorem check_R09p10_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 9 j%2 := by decide +kernel

private theorem check_R09p10_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 10 j%2 := by decide +kernel

private theorem check_R09p10_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 11 j%2 := by decide +kernel

private theorem check_R09p10_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 12 j%2 := by decide +kernel

private theorem check_R09p10_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 13 j%2 := by decide +kernel

private theorem check_R09p10_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 14 j%2 := by decide +kernel

private theorem check_R09p10_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 15 j%2 := by decide +kernel

private theorem check_R09p10_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 16 j%2 := by decide +kernel

private theorem check_R09p10_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 17 j%2 := by decide +kernel

private theorem check_R09p10_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 18 j%2 := by decide +kernel

private theorem check_R09p10_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 19 j%2 := by decide +kernel

private theorem check_R09p10_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 20 j%2 := by decide +kernel

private theorem check_R09p10_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit 21 j%2 := by decide +kernel

theorem checks_R09p10 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches09.R09p09_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R09p10_00 j
  · exact check_R09p10_01 j
  · exact check_R09p10_02 j
  · exact check_R09p10_03 j
  · exact check_R09p10_04 j
  · exact check_R09p10_05 j
  · exact check_R09p10_06 j
  · exact check_R09p10_07 j
  · exact check_R09p10_08 j
  · exact check_R09p10_09 j
  · exact check_R09p10_10 j
  · exact check_R09p10_11 j
  · exact check_R09p10_12 j
  · exact check_R09p10_13 j
  · exact check_R09p10_14 j
  · exact check_R09p10_15 j
  · exact check_R09p10_16 j
  · exact check_R09p10_17 j
  · exact check_R09p10_18 j
  · exact check_R09p10_19 j
  · exact check_R09p10_20 j
  · exact check_R09p10_21 j

def matrix_R09p10 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p09)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_R09p10 : matrix_R09p10=CFSGCoTwoNativeTwentyTwoCaches10.R09p10_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches09.R09p09_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches10.R09p10_data
    CFSGCoTwoNativeTwentyTwoProducts05.cache_R09p09 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_R09p10

private theorem check_R09p11_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 0 j%2 := by decide +kernel

private theorem check_R09p11_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 1 j%2 := by decide +kernel

private theorem check_R09p11_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 2 j%2 := by decide +kernel

private theorem check_R09p11_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 3 j%2 := by decide +kernel

private theorem check_R09p11_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 4 j%2 := by decide +kernel

private theorem check_R09p11_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 5 j%2 := by decide +kernel

private theorem check_R09p11_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 6 j%2 := by decide +kernel

private theorem check_R09p11_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 7 j%2 := by decide +kernel

private theorem check_R09p11_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 8 j%2 := by decide +kernel

private theorem check_R09p11_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 9 j%2 := by decide +kernel

private theorem check_R09p11_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 10 j%2 := by decide +kernel

private theorem check_R09p11_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 11 j%2 := by decide +kernel

private theorem check_R09p11_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 12 j%2 := by decide +kernel

private theorem check_R09p11_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 13 j%2 := by decide +kernel

private theorem check_R09p11_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 14 j%2 := by decide +kernel

private theorem check_R09p11_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 15 j%2 := by decide +kernel

private theorem check_R09p11_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 16 j%2 := by decide +kernel

private theorem check_R09p11_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 17 j%2 := by decide +kernel

private theorem check_R09p11_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 18 j%2 := by decide +kernel

private theorem check_R09p11_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 19 j%2 := by decide +kernel

private theorem check_R09p11_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 20 j%2 := by decide +kernel

private theorem check_R09p11_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit 21 j%2 := by decide +kernel

theorem checks_R09p11 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches10.R09p10_rowCode i*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R09p11_00 j
  · exact check_R09p11_01 j
  · exact check_R09p11_02 j
  · exact check_R09p11_03 j
  · exact check_R09p11_04 j
  · exact check_R09p11_05 j
  · exact check_R09p11_06 j
  · exact check_R09p11_07 j
  · exact check_R09p11_08 j
  · exact check_R09p11_09 j
  · exact check_R09p11_10 j
  · exact check_R09p11_11 j
  · exact check_R09p11_12 j
  · exact check_R09p11_13 j
  · exact check_R09p11_14 j
  · exact check_R09p11_15 j
  · exact check_R09p11_16 j
  · exact check_R09p11_17 j
  · exact check_R09p11_18 j
  · exact check_R09p11_19 j
  · exact check_R09p11_20 j
  · exact check_R09p11_21 j

def matrix_R09p11 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p10)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_B3)

theorem cache_R09p11 : matrix_R09p11=CFSGCoTwoNativeTwentyTwoCaches10.R09p11_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches10.R09p10_data CFSGCoTwoNativeTwentyTwoCaches00.B3_data CFSGCoTwoNativeTwentyTwoCaches10.R09p11_data
    CFSGCoTwoNativeTwentyTwoProducts05.cache_R09p10 CFSGCoTwoNativeTwentyTwoProducts00.cache_B3
    (by decide : 22*(2-1)^2<32) checks_R09p11

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts05
