import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches01
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoBaseCaches
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches03
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches04
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches00
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts00
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoPowerPilot
import Mathlib.Tactic.FinCases

/-! Fixed Co2 positive products; every whole matrix entry checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts02
open MatrixKroneckerProductReflection

private theorem check_R06p03_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 0 j%2 := by decide +kernel

private theorem check_R06p03_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 1 j%2 := by decide +kernel

private theorem check_R06p03_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 2 j%2 := by decide +kernel

private theorem check_R06p03_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 3 j%2 := by decide +kernel

private theorem check_R06p03_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 4 j%2 := by decide +kernel

private theorem check_R06p03_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 5 j%2 := by decide +kernel

private theorem check_R06p03_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 6 j%2 := by decide +kernel

private theorem check_R06p03_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 7 j%2 := by decide +kernel

private theorem check_R06p03_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 8 j%2 := by decide +kernel

private theorem check_R06p03_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 9 j%2 := by decide +kernel

private theorem check_R06p03_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 10 j%2 := by decide +kernel

private theorem check_R06p03_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 11 j%2 := by decide +kernel

private theorem check_R06p03_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 12 j%2 := by decide +kernel

private theorem check_R06p03_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 13 j%2 := by decide +kernel

private theorem check_R06p03_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 14 j%2 := by decide +kernel

private theorem check_R06p03_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 15 j%2 := by decide +kernel

private theorem check_R06p03_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 16 j%2 := by decide +kernel

private theorem check_R06p03_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 17 j%2 := by decide +kernel

private theorem check_R06p03_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 18 j%2 := by decide +kernel

private theorem check_R06p03_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 19 j%2 := by decide +kernel

private theorem check_R06p03_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 20 j%2 := by decide +kernel

private theorem check_R06p03_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit 21 j%2 := by decide +kernel

theorem checks_R06p03 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R06p03_00 j
  · exact check_R06p03_01 j
  · exact check_R06p03_02 j
  · exact check_R06p03_03 j
  · exact check_R06p03_04 j
  · exact check_R06p03_05 j
  · exact check_R06p03_06 j
  · exact check_R06p03_07 j
  · exact check_R06p03_08 j
  · exact check_R06p03_09 j
  · exact check_R06p03_10 j
  · exact check_R06p03_11 j
  · exact check_R06p03_12 j
  · exact check_R06p03_13 j
  · exact check_R06p03_14 j
  · exact check_R06p03_15 j
  · exact check_R06p03_16 j
  · exact check_R06p03_17 j
  · exact check_R06p03_18 j
  · exact check_R06p03_19 j
  · exact check_R06p03_20 j
  · exact check_R06p03_21 j

def matrix_R06p03 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts00.matrix_R04p02)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B4)

theorem cache_R06p03 : matrix_R06p03=CFSGCoTwoNativeTwentyTwoCaches03.R06p03_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches01.R04p02_data CFSGCoTwoNativeTwentyTwoBaseCaches.B4_data CFSGCoTwoNativeTwentyTwoCaches03.R06p03_data
    CFSGCoTwoNativeTwentyTwoProducts00.cache_R04p02 CFSGCoTwoNativeTwentyTwoPowerPilot.cache_B4
    (by decide : 22*(2-1)^2<32) checks_R06p03

private theorem check_R06p04_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 0 j%2 := by decide +kernel

private theorem check_R06p04_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 1 j%2 := by decide +kernel

private theorem check_R06p04_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 2 j%2 := by decide +kernel

private theorem check_R06p04_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 3 j%2 := by decide +kernel

private theorem check_R06p04_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 4 j%2 := by decide +kernel

private theorem check_R06p04_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 5 j%2 := by decide +kernel

private theorem check_R06p04_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 6 j%2 := by decide +kernel

private theorem check_R06p04_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 7 j%2 := by decide +kernel

private theorem check_R06p04_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 8 j%2 := by decide +kernel

private theorem check_R06p04_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 9 j%2 := by decide +kernel

private theorem check_R06p04_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 10 j%2 := by decide +kernel

private theorem check_R06p04_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 11 j%2 := by decide +kernel

private theorem check_R06p04_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 12 j%2 := by decide +kernel

private theorem check_R06p04_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 13 j%2 := by decide +kernel

private theorem check_R06p04_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 14 j%2 := by decide +kernel

private theorem check_R06p04_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 15 j%2 := by decide +kernel

private theorem check_R06p04_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 16 j%2 := by decide +kernel

private theorem check_R06p04_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 17 j%2 := by decide +kernel

private theorem check_R06p04_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 18 j%2 := by decide +kernel

private theorem check_R06p04_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 19 j%2 := by decide +kernel

private theorem check_R06p04_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 20 j%2 := by decide +kernel

private theorem check_R06p04_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit 21 j%2 := by decide +kernel

theorem checks_R06p04 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p03_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R06p04_00 j
  · exact check_R06p04_01 j
  · exact check_R06p04_02 j
  · exact check_R06p04_03 j
  · exact check_R06p04_04 j
  · exact check_R06p04_05 j
  · exact check_R06p04_06 j
  · exact check_R06p04_07 j
  · exact check_R06p04_08 j
  · exact check_R06p04_09 j
  · exact check_R06p04_10 j
  · exact check_R06p04_11 j
  · exact check_R06p04_12 j
  · exact check_R06p04_13 j
  · exact check_R06p04_14 j
  · exact check_R06p04_15 j
  · exact check_R06p04_16 j
  · exact check_R06p04_17 j
  · exact check_R06p04_18 j
  · exact check_R06p04_19 j
  · exact check_R06p04_20 j
  · exact check_R06p04_21 j

def matrix_R06p04 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p03)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_R06p04 : matrix_R06p04=CFSGCoTwoNativeTwentyTwoCaches03.R06p04_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches03.R06p03_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches03.R06p04_data
    CFSGCoTwoNativeTwentyTwoProducts02.cache_R06p03 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_R06p04

private theorem check_R06p05_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 0 j%2 := by decide +kernel

private theorem check_R06p05_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 1 j%2 := by decide +kernel

private theorem check_R06p05_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 2 j%2 := by decide +kernel

private theorem check_R06p05_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 3 j%2 := by decide +kernel

private theorem check_R06p05_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 4 j%2 := by decide +kernel

private theorem check_R06p05_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 5 j%2 := by decide +kernel

private theorem check_R06p05_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 6 j%2 := by decide +kernel

private theorem check_R06p05_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 7 j%2 := by decide +kernel

private theorem check_R06p05_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 8 j%2 := by decide +kernel

private theorem check_R06p05_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 9 j%2 := by decide +kernel

private theorem check_R06p05_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 10 j%2 := by decide +kernel

private theorem check_R06p05_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 11 j%2 := by decide +kernel

private theorem check_R06p05_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 12 j%2 := by decide +kernel

private theorem check_R06p05_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 13 j%2 := by decide +kernel

private theorem check_R06p05_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 14 j%2 := by decide +kernel

private theorem check_R06p05_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 15 j%2 := by decide +kernel

private theorem check_R06p05_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 16 j%2 := by decide +kernel

private theorem check_R06p05_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 17 j%2 := by decide +kernel

private theorem check_R06p05_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 18 j%2 := by decide +kernel

private theorem check_R06p05_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 19 j%2 := by decide +kernel

private theorem check_R06p05_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 20 j%2 := by decide +kernel

private theorem check_R06p05_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit 21 j%2 := by decide +kernel

theorem checks_R06p05 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p04_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R06p05_00 j
  · exact check_R06p05_01 j
  · exact check_R06p05_02 j
  · exact check_R06p05_03 j
  · exact check_R06p05_04 j
  · exact check_R06p05_05 j
  · exact check_R06p05_06 j
  · exact check_R06p05_07 j
  · exact check_R06p05_08 j
  · exact check_R06p05_09 j
  · exact check_R06p05_10 j
  · exact check_R06p05_11 j
  · exact check_R06p05_12 j
  · exact check_R06p05_13 j
  · exact check_R06p05_14 j
  · exact check_R06p05_15 j
  · exact check_R06p05_16 j
  · exact check_R06p05_17 j
  · exact check_R06p05_18 j
  · exact check_R06p05_19 j
  · exact check_R06p05_20 j
  · exact check_R06p05_21 j

def matrix_R06p05 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p04)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixB)

theorem cache_R06p05 : matrix_R06p05=CFSGCoTwoNativeTwentyTwoCaches03.R06p05_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches03.R06p04_data CFSGCoTwoNativeTwentyTwoBaseCaches.B_data CFSGCoTwoNativeTwentyTwoCaches03.R06p05_data
    CFSGCoTwoNativeTwentyTwoProducts02.cache_R06p04 CFSGCoTwoNativeTwentyTwoBaseCaches.B_source_binding
    (by decide : 22*(2-1)^2<32) checks_R06p05

private theorem check_R06p06_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 0 j%2 := by decide +kernel

private theorem check_R06p06_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 1 j%2 := by decide +kernel

private theorem check_R06p06_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 2 j%2 := by decide +kernel

private theorem check_R06p06_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 3 j%2 := by decide +kernel

private theorem check_R06p06_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 4 j%2 := by decide +kernel

private theorem check_R06p06_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 5 j%2 := by decide +kernel

private theorem check_R06p06_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 6 j%2 := by decide +kernel

private theorem check_R06p06_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 7 j%2 := by decide +kernel

private theorem check_R06p06_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 8 j%2 := by decide +kernel

private theorem check_R06p06_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 9 j%2 := by decide +kernel

private theorem check_R06p06_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 10 j%2 := by decide +kernel

private theorem check_R06p06_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 11 j%2 := by decide +kernel

private theorem check_R06p06_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 12 j%2 := by decide +kernel

private theorem check_R06p06_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 13 j%2 := by decide +kernel

private theorem check_R06p06_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 14 j%2 := by decide +kernel

private theorem check_R06p06_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 15 j%2 := by decide +kernel

private theorem check_R06p06_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 16 j%2 := by decide +kernel

private theorem check_R06p06_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 17 j%2 := by decide +kernel

private theorem check_R06p06_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 18 j%2 := by decide +kernel

private theorem check_R06p06_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 19 j%2 := by decide +kernel

private theorem check_R06p06_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 20 j%2 := by decide +kernel

private theorem check_R06p06_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit 21 j%2 := by decide +kernel

theorem checks_R06p06 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches03.R06p05_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R06p06_00 j
  · exact check_R06p06_01 j
  · exact check_R06p06_02 j
  · exact check_R06p06_03 j
  · exact check_R06p06_04 j
  · exact check_R06p06_05 j
  · exact check_R06p06_06 j
  · exact check_R06p06_07 j
  · exact check_R06p06_08 j
  · exact check_R06p06_09 j
  · exact check_R06p06_10 j
  · exact check_R06p06_11 j
  · exact check_R06p06_12 j
  · exact check_R06p06_13 j
  · exact check_R06p06_14 j
  · exact check_R06p06_15 j
  · exact check_R06p06_16 j
  · exact check_R06p06_17 j
  · exact check_R06p06_18 j
  · exact check_R06p06_19 j
  · exact check_R06p06_20 j
  · exact check_R06p06_21 j

def matrix_R06p06 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p05)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_R06p06 : matrix_R06p06=CFSGCoTwoNativeTwentyTwoCaches04.R06p06_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches03.R06p05_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches04.R06p06_data
    CFSGCoTwoNativeTwentyTwoProducts02.cache_R06p05 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_R06p06

private theorem check_R06p07_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 0 j%2 := by decide +kernel

private theorem check_R06p07_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 1 j%2 := by decide +kernel

private theorem check_R06p07_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 2 j%2 := by decide +kernel

private theorem check_R06p07_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 3 j%2 := by decide +kernel

private theorem check_R06p07_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 4 j%2 := by decide +kernel

private theorem check_R06p07_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 5 j%2 := by decide +kernel

private theorem check_R06p07_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 6 j%2 := by decide +kernel

private theorem check_R06p07_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 7 j%2 := by decide +kernel

private theorem check_R06p07_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 8 j%2 := by decide +kernel

private theorem check_R06p07_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 9 j%2 := by decide +kernel

private theorem check_R06p07_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 10 j%2 := by decide +kernel

private theorem check_R06p07_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 11 j%2 := by decide +kernel

private theorem check_R06p07_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 12 j%2 := by decide +kernel

private theorem check_R06p07_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 13 j%2 := by decide +kernel

private theorem check_R06p07_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 14 j%2 := by decide +kernel

private theorem check_R06p07_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 15 j%2 := by decide +kernel

private theorem check_R06p07_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 16 j%2 := by decide +kernel

private theorem check_R06p07_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 17 j%2 := by decide +kernel

private theorem check_R06p07_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 18 j%2 := by decide +kernel

private theorem check_R06p07_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 19 j%2 := by decide +kernel

private theorem check_R06p07_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 20 j%2 := by decide +kernel

private theorem check_R06p07_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit 21 j%2 := by decide +kernel

theorem checks_R06p07 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p06_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R06p07_00 j
  · exact check_R06p07_01 j
  · exact check_R06p07_02 j
  · exact check_R06p07_03 j
  · exact check_R06p07_04 j
  · exact check_R06p07_05 j
  · exact check_R06p07_06 j
  · exact check_R06p07_07 j
  · exact check_R06p07_08 j
  · exact check_R06p07_09 j
  · exact check_R06p07_10 j
  · exact check_R06p07_11 j
  · exact check_R06p07_12 j
  · exact check_R06p07_13 j
  · exact check_R06p07_14 j
  · exact check_R06p07_15 j
  · exact check_R06p07_16 j
  · exact check_R06p07_17 j
  · exact check_R06p07_18 j
  · exact check_R06p07_19 j
  · exact check_R06p07_20 j
  · exact check_R06p07_21 j

def matrix_R06p07 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p06)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixB)

theorem cache_R06p07 : matrix_R06p07=CFSGCoTwoNativeTwentyTwoCaches04.R06p07_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches04.R06p06_data CFSGCoTwoNativeTwentyTwoBaseCaches.B_data CFSGCoTwoNativeTwentyTwoCaches04.R06p07_data
    CFSGCoTwoNativeTwentyTwoProducts02.cache_R06p06 CFSGCoTwoNativeTwentyTwoBaseCaches.B_source_binding
    (by decide : 22*(2-1)^2<32) checks_R06p07

private theorem check_R06e02_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 0 j%2 := by decide +kernel

private theorem check_R06e02_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 1 j%2 := by decide +kernel

private theorem check_R06e02_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 2 j%2 := by decide +kernel

private theorem check_R06e02_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 3 j%2 := by decide +kernel

private theorem check_R06e02_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 4 j%2 := by decide +kernel

private theorem check_R06e02_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 5 j%2 := by decide +kernel

private theorem check_R06e02_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 6 j%2 := by decide +kernel

private theorem check_R06e02_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 7 j%2 := by decide +kernel

private theorem check_R06e02_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 8 j%2 := by decide +kernel

private theorem check_R06e02_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 9 j%2 := by decide +kernel

private theorem check_R06e02_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 10 j%2 := by decide +kernel

private theorem check_R06e02_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 11 j%2 := by decide +kernel

private theorem check_R06e02_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 12 j%2 := by decide +kernel

private theorem check_R06e02_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 13 j%2 := by decide +kernel

private theorem check_R06e02_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 14 j%2 := by decide +kernel

private theorem check_R06e02_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 15 j%2 := by decide +kernel

private theorem check_R06e02_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 16 j%2 := by decide +kernel

private theorem check_R06e02_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 17 j%2 := by decide +kernel

private theorem check_R06e02_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 18 j%2 := by decide +kernel

private theorem check_R06e02_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 19 j%2 := by decide +kernel

private theorem check_R06e02_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 20 j%2 := by decide +kernel

private theorem check_R06e02_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit 21 j%2 := by decide +kernel

theorem checks_R06e02 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06p07_rowCode i*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R06e02_00 j
  · exact check_R06e02_01 j
  · exact check_R06e02_02 j
  · exact check_R06e02_03 j
  · exact check_R06e02_04 j
  · exact check_R06e02_05 j
  · exact check_R06e02_06 j
  · exact check_R06e02_07 j
  · exact check_R06e02_08 j
  · exact check_R06e02_09 j
  · exact check_R06e02_10 j
  · exact check_R06e02_11 j
  · exact check_R06e02_12 j
  · exact check_R06e02_13 j
  · exact check_R06e02_14 j
  · exact check_R06e02_15 j
  · exact check_R06e02_16 j
  · exact check_R06e02_17 j
  · exact check_R06e02_18 j
  · exact check_R06e02_19 j
  · exact check_R06e02_20 j
  · exact check_R06e02_21 j

def matrix_R06e02 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p07)*(CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p07)

theorem cache_R06e02 : matrix_R06e02=CFSGCoTwoNativeTwentyTwoCaches04.R06e02_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches04.R06p07_data CFSGCoTwoNativeTwentyTwoCaches04.R06p07_data CFSGCoTwoNativeTwentyTwoCaches04.R06e02_data
    CFSGCoTwoNativeTwentyTwoProducts02.cache_R06p07 CFSGCoTwoNativeTwentyTwoProducts02.cache_R06p07
    (by decide : 22*(2-1)^2<32) checks_R06e02

private theorem check_R06e03_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 0 j%2 := by decide +kernel

private theorem check_R06e03_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 1 j%2 := by decide +kernel

private theorem check_R06e03_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 2 j%2 := by decide +kernel

private theorem check_R06e03_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 3 j%2 := by decide +kernel

private theorem check_R06e03_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 4 j%2 := by decide +kernel

private theorem check_R06e03_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 5 j%2 := by decide +kernel

private theorem check_R06e03_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 6 j%2 := by decide +kernel

private theorem check_R06e03_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 7 j%2 := by decide +kernel

private theorem check_R06e03_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 8 j%2 := by decide +kernel

private theorem check_R06e03_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 9 j%2 := by decide +kernel

private theorem check_R06e03_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 10 j%2 := by decide +kernel

private theorem check_R06e03_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 11 j%2 := by decide +kernel

private theorem check_R06e03_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 12 j%2 := by decide +kernel

private theorem check_R06e03_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 13 j%2 := by decide +kernel

private theorem check_R06e03_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 14 j%2 := by decide +kernel

private theorem check_R06e03_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 15 j%2 := by decide +kernel

private theorem check_R06e03_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 16 j%2 := by decide +kernel

private theorem check_R06e03_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 17 j%2 := by decide +kernel

private theorem check_R06e03_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 18 j%2 := by decide +kernel

private theorem check_R06e03_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 19 j%2 := by decide +kernel

private theorem check_R06e03_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 20 j%2 := by decide +kernel

private theorem check_R06e03_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 21 j%2 := by decide +kernel

theorem checks_R06e03 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches04.R06e02_rowCode i*CFSGCoTwoNativeTwentyTwoCaches04.R06p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R06e03_00 j
  · exact check_R06e03_01 j
  · exact check_R06e03_02 j
  · exact check_R06e03_03 j
  · exact check_R06e03_04 j
  · exact check_R06e03_05 j
  · exact check_R06e03_06 j
  · exact check_R06e03_07 j
  · exact check_R06e03_08 j
  · exact check_R06e03_09 j
  · exact check_R06e03_10 j
  · exact check_R06e03_11 j
  · exact check_R06e03_12 j
  · exact check_R06e03_13 j
  · exact check_R06e03_14 j
  · exact check_R06e03_15 j
  · exact check_R06e03_16 j
  · exact check_R06e03_17 j
  · exact check_R06e03_18 j
  · exact check_R06e03_19 j
  · exact check_R06e03_20 j
  · exact check_R06e03_21 j

def matrix_R06e03 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06e02)*(CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p07)

theorem cache_R06e03 : matrix_R06e03=CFSGCoTwoNativeTwentyTwoBaseCaches.I_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches04.R06e02_data CFSGCoTwoNativeTwentyTwoCaches04.R06p07_data CFSGCoTwoNativeTwentyTwoBaseCaches.I_data
    CFSGCoTwoNativeTwentyTwoProducts02.cache_R06e02 CFSGCoTwoNativeTwentyTwoProducts02.cache_R06p07
    (by decide : 22*(2-1)^2<32) checks_R06e03

private theorem check_R07p03_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 0 j%2 := by decide +kernel

private theorem check_R07p03_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 1 j%2 := by decide +kernel

private theorem check_R07p03_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 2 j%2 := by decide +kernel

private theorem check_R07p03_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 3 j%2 := by decide +kernel

private theorem check_R07p03_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 4 j%2 := by decide +kernel

private theorem check_R07p03_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 5 j%2 := by decide +kernel

private theorem check_R07p03_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 6 j%2 := by decide +kernel

private theorem check_R07p03_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 7 j%2 := by decide +kernel

private theorem check_R07p03_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 8 j%2 := by decide +kernel

private theorem check_R07p03_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 9 j%2 := by decide +kernel

private theorem check_R07p03_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 10 j%2 := by decide +kernel

private theorem check_R07p03_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 11 j%2 := by decide +kernel

private theorem check_R07p03_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 12 j%2 := by decide +kernel

private theorem check_R07p03_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 13 j%2 := by decide +kernel

private theorem check_R07p03_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 14 j%2 := by decide +kernel

private theorem check_R07p03_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 15 j%2 := by decide +kernel

private theorem check_R07p03_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 16 j%2 := by decide +kernel

private theorem check_R07p03_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 17 j%2 := by decide +kernel

private theorem check_R07p03_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 18 j%2 := by decide +kernel

private theorem check_R07p03_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 19 j%2 := by decide +kernel

private theorem check_R07p03_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 20 j%2 := by decide +kernel

private theorem check_R07p03_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit 21 j%2 := by decide +kernel

theorem checks_R07p03 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches01.R04p02_rowCode i*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R07p03_00 j
  · exact check_R07p03_01 j
  · exact check_R07p03_02 j
  · exact check_R07p03_03 j
  · exact check_R07p03_04 j
  · exact check_R07p03_05 j
  · exact check_R07p03_06 j
  · exact check_R07p03_07 j
  · exact check_R07p03_08 j
  · exact check_R07p03_09 j
  · exact check_R07p03_10 j
  · exact check_R07p03_11 j
  · exact check_R07p03_12 j
  · exact check_R07p03_13 j
  · exact check_R07p03_14 j
  · exact check_R07p03_15 j
  · exact check_R07p03_16 j
  · exact check_R07p03_17 j
  · exact check_R07p03_18 j
  · exact check_R07p03_19 j
  · exact check_R07p03_20 j
  · exact check_R07p03_21 j

def matrix_R07p03 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts00.matrix_R04p02)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_B3)

theorem cache_R07p03 : matrix_R07p03=CFSGCoTwoNativeTwentyTwoCaches04.R07p03_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches01.R04p02_data CFSGCoTwoNativeTwentyTwoCaches00.B3_data CFSGCoTwoNativeTwentyTwoCaches04.R07p03_data
    CFSGCoTwoNativeTwentyTwoProducts00.cache_R04p02 CFSGCoTwoNativeTwentyTwoProducts00.cache_B3
    (by decide : 22*(2-1)^2<32) checks_R07p03

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts02
