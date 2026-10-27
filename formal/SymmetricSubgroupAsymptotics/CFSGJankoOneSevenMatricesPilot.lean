import SymmetricSubgroupAsymptotics.SmallNaturalMatrixProductReflection
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Literal7/F11 images from the selected raw Meataxe diagnostic.
The definitions are coefficients, not a named-model identification.
Only the first two whole relators and one nonidentity entry are claimed. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoOneSevenMatrices
open SmallNaturalMatrixProductReflection
abbrev M := Matrix (Fin 7) (Fin 7) (ZMod 11)
def rawA : Matrix (Fin 7) (Fin 7) ℕ := !![
  0,7,9,9,10,7,9;
  7,0,1,4,3,3,4;
  9,1,2,8,3,6,2;
  9,4,8,10,1,6,0;
  10,3,3,1,8,9,1;
  7,3,6,6,9,1,3;
  9,4,2,0,1,3,0]
def rawB : Matrix (Fin 7) (Fin 7) ℕ := !![
  5,7,1,8,5,8,2;
  10,4,10,0,3,3,8;
  5,10,8,9,1,2,1;
  2,3,3,6,1,2,9;
  7,4,7,2,10,7,3;
  3,9,0,4,2,3,5;
  3,4,3,3,9,4,9]
def matrixA : M := castMatrix 11 7 rawA
def matrixB : M := castMatrix 11 7 rawB

private theorem check_AA : ∀ i j : Fin 7,
    (∑ k : Fin 7,rawA i k*rawA k j)%11=(1 : Matrix (Fin 7) (Fin 7) ℕ) i j%11 := by
  decide +kernel

private theorem check_BBB : ∀ i j : Fin 7,
    (∑ k : Fin 7,(rawB*rawB) i k*rawB k j)%11=(1 : Matrix (Fin 7) (Fin 7) ℕ) i j%11 := by
  decide +kernel

theorem matrixA_square : matrixA^2=1 := by
  rw [pow_two]
  exact (mul_eq_of_mod_dot 11 7 rawA rawA 1 check_AA).trans (castMatrix_one 11 7)

theorem matrixB_cube : matrixB^3=1 := by
  rw [pow_succ,pow_two]
  change (castMatrix 11 7 rawB*castMatrix 11 7 rawB)*castMatrix 11 7 rawB=1
  rw [←castMatrix_mul]
  exact (mul_eq_of_mod_dot 11 7 (rawB*rawB) rawB 1 check_BBB).trans (castMatrix_one 11 7)

theorem matrixA_ne_one : matrixA≠1 := by
  intro h
  have hn : matrixA (0 : Fin 7) 0≠(1 : M) 0 0 := by decide +kernel
  exact hn (congrArg (fun z : M => z 0 0) h)

def unitA : Matrix.GeneralLinearGroup (Fin 7) (ZMod 11) where
  val := matrixA
  inv := matrixA
  val_inv := by simpa only [pow_two] using matrixA_square
  inv_val := by simpa only [pow_two] using matrixA_square

def unitB : Matrix.GeneralLinearGroup (Fin 7) (ZMod 11) where
  val := matrixB
  inv := matrixB^2
  val_inv := (pow_succ' matrixB 2).symm.trans matrixB_cube
  inv_val := (pow_succ matrixB 2).symm.trans matrixB_cube

theorem unitA_ne_one : unitA≠1 := by
  intro h
  apply matrixA_ne_one
  exact congrArg (fun z : Matrix.GeneralLinearGroup (Fin 7) (ZMod 11) => (z : M)) h

end SymmetricSubgroupAsymptotics.CFSGJankoOneSevenMatrices
