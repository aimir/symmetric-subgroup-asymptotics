import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches06
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoBaseCaches
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches00
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches07
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches08
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts03
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts00
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoPowerPilot
import Mathlib.Tactic.FinCases

/-! Fixed Co2 positive products; every whole matrix entry checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts04
open MatrixKroneckerProductReflection

private theorem check_R07e02_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 0 j%2 := by decide +kernel

private theorem check_R07e02_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 1 j%2 := by decide +kernel

private theorem check_R07e02_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 2 j%2 := by decide +kernel

private theorem check_R07e02_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 3 j%2 := by decide +kernel

private theorem check_R07e02_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 4 j%2 := by decide +kernel

private theorem check_R07e02_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 5 j%2 := by decide +kernel

private theorem check_R07e02_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 6 j%2 := by decide +kernel

private theorem check_R07e02_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 7 j%2 := by decide +kernel

private theorem check_R07e02_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 8 j%2 := by decide +kernel

private theorem check_R07e02_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 9 j%2 := by decide +kernel

private theorem check_R07e02_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 10 j%2 := by decide +kernel

private theorem check_R07e02_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 11 j%2 := by decide +kernel

private theorem check_R07e02_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 12 j%2 := by decide +kernel

private theorem check_R07e02_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 13 j%2 := by decide +kernel

private theorem check_R07e02_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 14 j%2 := by decide +kernel

private theorem check_R07e02_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 15 j%2 := by decide +kernel

private theorem check_R07e02_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 16 j%2 := by decide +kernel

private theorem check_R07e02_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 17 j%2 := by decide +kernel

private theorem check_R07e02_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 18 j%2 := by decide +kernel

private theorem check_R07e02_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 19 j%2 := by decide +kernel

private theorem check_R07e02_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 20 j%2 := by decide +kernel

private theorem check_R07e02_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit 21 j%2 := by decide +kernel

theorem checks_R07e02 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches06.R07p11_rowCode i*CFSGCoTwoNativeTwentyTwoCaches06.R07p11_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoBaseCaches.I_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R07e02_00 j
  · exact check_R07e02_01 j
  · exact check_R07e02_02 j
  · exact check_R07e02_03 j
  · exact check_R07e02_04 j
  · exact check_R07e02_05 j
  · exact check_R07e02_06 j
  · exact check_R07e02_07 j
  · exact check_R07e02_08 j
  · exact check_R07e02_09 j
  · exact check_R07e02_10 j
  · exact check_R07e02_11 j
  · exact check_R07e02_12 j
  · exact check_R07e02_13 j
  · exact check_R07e02_14 j
  · exact check_R07e02_15 j
  · exact check_R07e02_16 j
  · exact check_R07e02_17 j
  · exact check_R07e02_18 j
  · exact check_R07e02_19 j
  · exact check_R07e02_20 j
  · exact check_R07e02_21 j

def matrix_R07e02 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p11)*(CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p11)

theorem cache_R07e02 : matrix_R07e02=CFSGCoTwoNativeTwentyTwoBaseCaches.I_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches06.R07p11_data CFSGCoTwoNativeTwentyTwoCaches06.R07p11_data CFSGCoTwoNativeTwentyTwoBaseCaches.I_data
    CFSGCoTwoNativeTwentyTwoProducts03.cache_R07p11 CFSGCoTwoNativeTwentyTwoProducts03.cache_R07p11
    (by decide : 22*(2-1)^2<32) checks_R07e02

private theorem check_R08p02_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 0 j%2 := by decide +kernel

private theorem check_R08p02_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 1 j%2 := by decide +kernel

private theorem check_R08p02_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 2 j%2 := by decide +kernel

private theorem check_R08p02_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 3 j%2 := by decide +kernel

private theorem check_R08p02_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 4 j%2 := by decide +kernel

private theorem check_R08p02_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 5 j%2 := by decide +kernel

private theorem check_R08p02_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 6 j%2 := by decide +kernel

private theorem check_R08p02_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 7 j%2 := by decide +kernel

private theorem check_R08p02_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 8 j%2 := by decide +kernel

private theorem check_R08p02_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 9 j%2 := by decide +kernel

private theorem check_R08p02_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 10 j%2 := by decide +kernel

private theorem check_R08p02_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 11 j%2 := by decide +kernel

private theorem check_R08p02_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 12 j%2 := by decide +kernel

private theorem check_R08p02_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 13 j%2 := by decide +kernel

private theorem check_R08p02_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 14 j%2 := by decide +kernel

private theorem check_R08p02_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 15 j%2 := by decide +kernel

private theorem check_R08p02_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 16 j%2 := by decide +kernel

private theorem check_R08p02_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 17 j%2 := by decide +kernel

private theorem check_R08p02_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 18 j%2 := by decide +kernel

private theorem check_R08p02_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 19 j%2 := by decide +kernel

private theorem check_R08p02_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 20 j%2 := by decide +kernel

private theorem check_R08p02_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit 21 j%2 := by decide +kernel

theorem checks_R08p02 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches00.R03p01_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R08p02_00 j
  · exact check_R08p02_01 j
  · exact check_R08p02_02 j
  · exact check_R08p02_03 j
  · exact check_R08p02_04 j
  · exact check_R08p02_05 j
  · exact check_R08p02_06 j
  · exact check_R08p02_07 j
  · exact check_R08p02_08 j
  · exact check_R08p02_09 j
  · exact check_R08p02_10 j
  · exact check_R08p02_11 j
  · exact check_R08p02_12 j
  · exact check_R08p02_13 j
  · exact check_R08p02_14 j
  · exact check_R08p02_15 j
  · exact check_R08p02_16 j
  · exact check_R08p02_17 j
  · exact check_R08p02_18 j
  · exact check_R08p02_19 j
  · exact check_R08p02_20 j
  · exact check_R08p02_21 j

def matrix_R08p02 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03p01)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_R08p02 : matrix_R08p02=CFSGCoTwoNativeTwentyTwoCaches07.R08p02_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches00.R03p01_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches07.R08p02_data
    CFSGCoTwoNativeTwentyTwoProducts00.cache_R03p01 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_R08p02

private theorem check_R08p03_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 0 j%2 := by decide +kernel

private theorem check_R08p03_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 1 j%2 := by decide +kernel

private theorem check_R08p03_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 2 j%2 := by decide +kernel

private theorem check_R08p03_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 3 j%2 := by decide +kernel

private theorem check_R08p03_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 4 j%2 := by decide +kernel

private theorem check_R08p03_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 5 j%2 := by decide +kernel

private theorem check_R08p03_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 6 j%2 := by decide +kernel

private theorem check_R08p03_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 7 j%2 := by decide +kernel

private theorem check_R08p03_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 8 j%2 := by decide +kernel

private theorem check_R08p03_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 9 j%2 := by decide +kernel

private theorem check_R08p03_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 10 j%2 := by decide +kernel

private theorem check_R08p03_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 11 j%2 := by decide +kernel

private theorem check_R08p03_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 12 j%2 := by decide +kernel

private theorem check_R08p03_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 13 j%2 := by decide +kernel

private theorem check_R08p03_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 14 j%2 := by decide +kernel

private theorem check_R08p03_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 15 j%2 := by decide +kernel

private theorem check_R08p03_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 16 j%2 := by decide +kernel

private theorem check_R08p03_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 17 j%2 := by decide +kernel

private theorem check_R08p03_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 18 j%2 := by decide +kernel

private theorem check_R08p03_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 19 j%2 := by decide +kernel

private theorem check_R08p03_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 20 j%2 := by decide +kernel

private theorem check_R08p03_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit 21 j%2 := by decide +kernel

theorem checks_R08p03 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p02_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B4_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R08p03_00 j
  · exact check_R08p03_01 j
  · exact check_R08p03_02 j
  · exact check_R08p03_03 j
  · exact check_R08p03_04 j
  · exact check_R08p03_05 j
  · exact check_R08p03_06 j
  · exact check_R08p03_07 j
  · exact check_R08p03_08 j
  · exact check_R08p03_09 j
  · exact check_R08p03_10 j
  · exact check_R08p03_11 j
  · exact check_R08p03_12 j
  · exact check_R08p03_13 j
  · exact check_R08p03_14 j
  · exact check_R08p03_15 j
  · exact check_R08p03_16 j
  · exact check_R08p03_17 j
  · exact check_R08p03_18 j
  · exact check_R08p03_19 j
  · exact check_R08p03_20 j
  · exact check_R08p03_21 j

def matrix_R08p03 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p02)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B4)

theorem cache_R08p03 : matrix_R08p03=CFSGCoTwoNativeTwentyTwoCaches07.R08p03_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches07.R08p02_data CFSGCoTwoNativeTwentyTwoBaseCaches.B4_data CFSGCoTwoNativeTwentyTwoCaches07.R08p03_data
    CFSGCoTwoNativeTwentyTwoProducts04.cache_R08p02 CFSGCoTwoNativeTwentyTwoPowerPilot.cache_B4
    (by decide : 22*(2-1)^2<32) checks_R08p03

private theorem check_R08p04_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 0 j%2 := by decide +kernel

private theorem check_R08p04_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 1 j%2 := by decide +kernel

private theorem check_R08p04_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 2 j%2 := by decide +kernel

private theorem check_R08p04_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 3 j%2 := by decide +kernel

private theorem check_R08p04_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 4 j%2 := by decide +kernel

private theorem check_R08p04_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 5 j%2 := by decide +kernel

private theorem check_R08p04_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 6 j%2 := by decide +kernel

private theorem check_R08p04_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 7 j%2 := by decide +kernel

private theorem check_R08p04_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 8 j%2 := by decide +kernel

private theorem check_R08p04_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 9 j%2 := by decide +kernel

private theorem check_R08p04_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 10 j%2 := by decide +kernel

private theorem check_R08p04_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 11 j%2 := by decide +kernel

private theorem check_R08p04_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 12 j%2 := by decide +kernel

private theorem check_R08p04_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 13 j%2 := by decide +kernel

private theorem check_R08p04_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 14 j%2 := by decide +kernel

private theorem check_R08p04_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 15 j%2 := by decide +kernel

private theorem check_R08p04_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 16 j%2 := by decide +kernel

private theorem check_R08p04_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 17 j%2 := by decide +kernel

private theorem check_R08p04_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 18 j%2 := by decide +kernel

private theorem check_R08p04_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 19 j%2 := by decide +kernel

private theorem check_R08p04_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 20 j%2 := by decide +kernel

private theorem check_R08p04_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit 21 j%2 := by decide +kernel

theorem checks_R08p04 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p03_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R08p04_00 j
  · exact check_R08p04_01 j
  · exact check_R08p04_02 j
  · exact check_R08p04_03 j
  · exact check_R08p04_04 j
  · exact check_R08p04_05 j
  · exact check_R08p04_06 j
  · exact check_R08p04_07 j
  · exact check_R08p04_08 j
  · exact check_R08p04_09 j
  · exact check_R08p04_10 j
  · exact check_R08p04_11 j
  · exact check_R08p04_12 j
  · exact check_R08p04_13 j
  · exact check_R08p04_14 j
  · exact check_R08p04_15 j
  · exact check_R08p04_16 j
  · exact check_R08p04_17 j
  · exact check_R08p04_18 j
  · exact check_R08p04_19 j
  · exact check_R08p04_20 j
  · exact check_R08p04_21 j

def matrix_R08p04 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p03)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_R08p04 : matrix_R08p04=CFSGCoTwoNativeTwentyTwoCaches07.R08p04_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches07.R08p03_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches07.R08p04_data
    CFSGCoTwoNativeTwentyTwoProducts04.cache_R08p03 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_R08p04

private theorem check_R08p05_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 0 j%2 := by decide +kernel

private theorem check_R08p05_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 1 j%2 := by decide +kernel

private theorem check_R08p05_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 2 j%2 := by decide +kernel

private theorem check_R08p05_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 3 j%2 := by decide +kernel

private theorem check_R08p05_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 4 j%2 := by decide +kernel

private theorem check_R08p05_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 5 j%2 := by decide +kernel

private theorem check_R08p05_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 6 j%2 := by decide +kernel

private theorem check_R08p05_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 7 j%2 := by decide +kernel

private theorem check_R08p05_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 8 j%2 := by decide +kernel

private theorem check_R08p05_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 9 j%2 := by decide +kernel

private theorem check_R08p05_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 10 j%2 := by decide +kernel

private theorem check_R08p05_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 11 j%2 := by decide +kernel

private theorem check_R08p05_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 12 j%2 := by decide +kernel

private theorem check_R08p05_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 13 j%2 := by decide +kernel

private theorem check_R08p05_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 14 j%2 := by decide +kernel

private theorem check_R08p05_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 15 j%2 := by decide +kernel

private theorem check_R08p05_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 16 j%2 := by decide +kernel

private theorem check_R08p05_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 17 j%2 := by decide +kernel

private theorem check_R08p05_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 18 j%2 := by decide +kernel

private theorem check_R08p05_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 19 j%2 := by decide +kernel

private theorem check_R08p05_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 20 j%2 := by decide +kernel

private theorem check_R08p05_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit 21 j%2 := by decide +kernel

theorem checks_R08p05 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p04_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.B_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R08p05_00 j
  · exact check_R08p05_01 j
  · exact check_R08p05_02 j
  · exact check_R08p05_03 j
  · exact check_R08p05_04 j
  · exact check_R08p05_05 j
  · exact check_R08p05_06 j
  · exact check_R08p05_07 j
  · exact check_R08p05_08 j
  · exact check_R08p05_09 j
  · exact check_R08p05_10 j
  · exact check_R08p05_11 j
  · exact check_R08p05_12 j
  · exact check_R08p05_13 j
  · exact check_R08p05_14 j
  · exact check_R08p05_15 j
  · exact check_R08p05_16 j
  · exact check_R08p05_17 j
  · exact check_R08p05_18 j
  · exact check_R08p05_19 j
  · exact check_R08p05_20 j
  · exact check_R08p05_21 j

def matrix_R08p05 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p04)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixB)

theorem cache_R08p05 : matrix_R08p05=CFSGCoTwoNativeTwentyTwoCaches07.R08p05_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches07.R08p04_data CFSGCoTwoNativeTwentyTwoBaseCaches.B_data CFSGCoTwoNativeTwentyTwoCaches07.R08p05_data
    CFSGCoTwoNativeTwentyTwoProducts04.cache_R08p04 CFSGCoTwoNativeTwentyTwoBaseCaches.B_source_binding
    (by decide : 22*(2-1)^2<32) checks_R08p05

private theorem check_R08p06_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 0*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 0 j%2 := by decide +kernel

private theorem check_R08p06_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 1*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 1 j%2 := by decide +kernel

private theorem check_R08p06_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 2*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 2 j%2 := by decide +kernel

private theorem check_R08p06_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 3*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 3 j%2 := by decide +kernel

private theorem check_R08p06_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 4*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 4 j%2 := by decide +kernel

private theorem check_R08p06_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 5*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 5 j%2 := by decide +kernel

private theorem check_R08p06_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 6*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 6 j%2 := by decide +kernel

private theorem check_R08p06_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 7*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 7 j%2 := by decide +kernel

private theorem check_R08p06_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 8*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 8 j%2 := by decide +kernel

private theorem check_R08p06_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 9*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 9 j%2 := by decide +kernel

private theorem check_R08p06_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 10*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 10 j%2 := by decide +kernel

private theorem check_R08p06_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 11*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 11 j%2 := by decide +kernel

private theorem check_R08p06_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 12*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 12 j%2 := by decide +kernel

private theorem check_R08p06_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 13*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 13 j%2 := by decide +kernel

private theorem check_R08p06_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 14*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 14 j%2 := by decide +kernel

private theorem check_R08p06_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 15*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 15 j%2 := by decide +kernel

private theorem check_R08p06_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 16*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 16 j%2 := by decide +kernel

private theorem check_R08p06_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 17*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 17 j%2 := by decide +kernel

private theorem check_R08p06_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 18*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 18 j%2 := by decide +kernel

private theorem check_R08p06_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 19*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 19 j%2 := by decide +kernel

private theorem check_R08p06_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 20*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 20 j%2 := by decide +kernel

private theorem check_R08p06_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode 21*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit 21 j%2 := by decide +kernel

theorem checks_R08p06 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches07.R08p05_rowCode i*CFSGCoTwoNativeTwentyTwoBaseCaches.A_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R08p06_00 j
  · exact check_R08p06_01 j
  · exact check_R08p06_02 j
  · exact check_R08p06_03 j
  · exact check_R08p06_04 j
  · exact check_R08p06_05 j
  · exact check_R08p06_06 j
  · exact check_R08p06_07 j
  · exact check_R08p06_08 j
  · exact check_R08p06_09 j
  · exact check_R08p06_10 j
  · exact check_R08p06_11 j
  · exact check_R08p06_12 j
  · exact check_R08p06_13 j
  · exact check_R08p06_14 j
  · exact check_R08p06_15 j
  · exact check_R08p06_16 j
  · exact check_R08p06_17 j
  · exact check_R08p06_18 j
  · exact check_R08p06_19 j
  · exact check_R08p06_20 j
  · exact check_R08p06_21 j

def matrix_R08p06 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p05)*(CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA)

theorem cache_R08p06 : matrix_R08p06=CFSGCoTwoNativeTwentyTwoCaches08.R08p06_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches07.R08p05_data CFSGCoTwoNativeTwentyTwoBaseCaches.A_data CFSGCoTwoNativeTwentyTwoCaches08.R08p06_data
    CFSGCoTwoNativeTwentyTwoProducts04.cache_R08p05 CFSGCoTwoNativeTwentyTwoBaseCaches.A_source_binding
    (by decide : 22*(2-1)^2<32) checks_R08p06

private theorem check_R08p07_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 0 j%2 := by decide +kernel

private theorem check_R08p07_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 1 j%2 := by decide +kernel

private theorem check_R08p07_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 2 j%2 := by decide +kernel

private theorem check_R08p07_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 3 j%2 := by decide +kernel

private theorem check_R08p07_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 4 j%2 := by decide +kernel

private theorem check_R08p07_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 5 j%2 := by decide +kernel

private theorem check_R08p07_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 6 j%2 := by decide +kernel

private theorem check_R08p07_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 7 j%2 := by decide +kernel

private theorem check_R08p07_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 8 j%2 := by decide +kernel

private theorem check_R08p07_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 9 j%2 := by decide +kernel

private theorem check_R08p07_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 10 j%2 := by decide +kernel

private theorem check_R08p07_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 11 j%2 := by decide +kernel

private theorem check_R08p07_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 12 j%2 := by decide +kernel

private theorem check_R08p07_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 13 j%2 := by decide +kernel

private theorem check_R08p07_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 14 j%2 := by decide +kernel

private theorem check_R08p07_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 15 j%2 := by decide +kernel

private theorem check_R08p07_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 16 j%2 := by decide +kernel

private theorem check_R08p07_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 17 j%2 := by decide +kernel

private theorem check_R08p07_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 18 j%2 := by decide +kernel

private theorem check_R08p07_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 19 j%2 := by decide +kernel

private theorem check_R08p07_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 20 j%2 := by decide +kernel

private theorem check_R08p07_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit 21 j%2 := by decide +kernel

theorem checks_R08p07 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p06_rowCode i*CFSGCoTwoNativeTwentyTwoCaches00.B3_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R08p07_00 j
  · exact check_R08p07_01 j
  · exact check_R08p07_02 j
  · exact check_R08p07_03 j
  · exact check_R08p07_04 j
  · exact check_R08p07_05 j
  · exact check_R08p07_06 j
  · exact check_R08p07_07 j
  · exact check_R08p07_08 j
  · exact check_R08p07_09 j
  · exact check_R08p07_10 j
  · exact check_R08p07_11 j
  · exact check_R08p07_12 j
  · exact check_R08p07_13 j
  · exact check_R08p07_14 j
  · exact check_R08p07_15 j
  · exact check_R08p07_16 j
  · exact check_R08p07_17 j
  · exact check_R08p07_18 j
  · exact check_R08p07_19 j
  · exact check_R08p07_20 j
  · exact check_R08p07_21 j

def matrix_R08p07 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p06)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_B3)

theorem cache_R08p07 : matrix_R08p07=CFSGCoTwoNativeTwentyTwoCaches08.R08p07_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches08.R08p06_data CFSGCoTwoNativeTwentyTwoCaches00.B3_data CFSGCoTwoNativeTwentyTwoCaches08.R08p07_data
    CFSGCoTwoNativeTwentyTwoProducts04.cache_R08p06 CFSGCoTwoNativeTwentyTwoProducts00.cache_B3
    (by decide : 22*(2-1)^2<32) checks_R08p07

private theorem check_R08e02_00 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 0*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 0 j%2 := by decide +kernel

private theorem check_R08e02_01 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 1*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 1 j%2 := by decide +kernel

private theorem check_R08e02_02 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 2*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 2 j%2 := by decide +kernel

private theorem check_R08e02_03 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 3*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 3 j%2 := by decide +kernel

private theorem check_R08e02_04 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 4*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 4 j%2 := by decide +kernel

private theorem check_R08e02_05 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 5*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 5 j%2 := by decide +kernel

private theorem check_R08e02_06 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 6*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 6 j%2 := by decide +kernel

private theorem check_R08e02_07 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 7*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 7 j%2 := by decide +kernel

private theorem check_R08e02_08 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 8*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 8 j%2 := by decide +kernel

private theorem check_R08e02_09 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 9*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 9 j%2 := by decide +kernel

private theorem check_R08e02_10 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 10*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 10 j%2 := by decide +kernel

private theorem check_R08e02_11 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 11*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 11 j%2 := by decide +kernel

private theorem check_R08e02_12 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 12*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 12 j%2 := by decide +kernel

private theorem check_R08e02_13 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 13*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 13 j%2 := by decide +kernel

private theorem check_R08e02_14 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 14*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 14 j%2 := by decide +kernel

private theorem check_R08e02_15 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 15*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 15 j%2 := by decide +kernel

private theorem check_R08e02_16 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 16*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 16 j%2 := by decide +kernel

private theorem check_R08e02_17 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 17*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 17 j%2 := by decide +kernel

private theorem check_R08e02_18 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 18*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 18 j%2 := by decide +kernel

private theorem check_R08e02_19 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 19*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 19 j%2 := by decide +kernel

private theorem check_R08e02_20 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 20*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 20 j%2 := by decide +kernel

private theorem check_R08e02_21 : ∀ j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode 21*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit 21 j%2 := by decide +kernel

theorem checks_R08e02 : ∀ i j : Fin 22,
    (((CFSGCoTwoNativeTwentyTwoCaches08.R08p07_rowCode i*CFSGCoTwoNativeTwentyTwoCaches08.R08p07_columnCode j)/32^21)%32)%2=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_digit i j%2 := by
  intro i j
  fin_cases i
  · exact check_R08e02_00 j
  · exact check_R08e02_01 j
  · exact check_R08e02_02 j
  · exact check_R08e02_03 j
  · exact check_R08e02_04 j
  · exact check_R08e02_05 j
  · exact check_R08e02_06 j
  · exact check_R08e02_07 j
  · exact check_R08e02_08 j
  · exact check_R08e02_09 j
  · exact check_R08e02_10 j
  · exact check_R08e02_11 j
  · exact check_R08e02_12 j
  · exact check_R08e02_13 j
  · exact check_R08e02_14 j
  · exact check_R08e02_15 j
  · exact check_R08e02_16 j
  · exact check_R08e02_17 j
  · exact check_R08e02_18 j
  · exact check_R08e02_19 j
  · exact check_R08e02_20 j
  · exact check_R08e02_21 j

def matrix_R08e02 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  (CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p07)*(CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p07)

theorem cache_R08e02 : matrix_R08e02=CFSGCoTwoNativeTwentyTwoCaches08.R08e02_data.matrix 2 := by
  exact product_eq_of_data (by decide : 0<22) _ _
    CFSGCoTwoNativeTwentyTwoCaches08.R08p07_data CFSGCoTwoNativeTwentyTwoCaches08.R08p07_data CFSGCoTwoNativeTwentyTwoCaches08.R08e02_data
    CFSGCoTwoNativeTwentyTwoProducts04.cache_R08p07 CFSGCoTwoNativeTwentyTwoProducts04.cache_R08p07
    (by decide : 22*(2-1)^2<32) checks_R08e02

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts04
