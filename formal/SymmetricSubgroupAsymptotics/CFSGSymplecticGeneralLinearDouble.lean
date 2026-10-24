import SymmetricSubgroupAsymptotics.CFSGSymplecticFullGroup
import SymmetricSubgroupAsymptotics.CFSGMatrixShearUnits
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! The literal GL double diag(A,A^{-transpose}) belongs to the SAME
original elementary symplectic group, over every field. Its actual
conjugation on upper shears is symmetric-matrix congruence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticGeneralLinearDouble

open CFSGSymplecticSerreMatrices
variable (K : Type) [Field K] (n : ℕ)

abbrev GeneralLinear := (Matrix (Fin n) (Fin n) K)ˣ

def doubleMatrix (A : GeneralLinear K n) : Mat K n :=
  Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose

theorem doubleMatrix_one : doubleMatrix K n 1 = 1 := by
  change Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) K) 0 0
    (1 : Matrix (Fin n) (Fin n) K).transpose = 1
  rw [Matrix.transpose_one, Matrix.fromBlocks_one]

theorem doubleMatrix_mul (A B : GeneralLinear K n) :
    doubleMatrix K n (A * B) = doubleMatrix K n A * doubleMatrix K n B := by
  unfold doubleMatrix
  rw [mul_inv_rev]
  change Matrix.fromBlocks (A.val * B.val) 0 0
    ((B⁻¹).val * (A⁻¹).val).transpose =
    Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose *
      Matrix.fromBlocks B.val 0 0 (B⁻¹).val.transpose
  rw [Matrix.fromBlocks_multiply, Matrix.transpose_mul]
  simp only [mul_zero, zero_mul, add_zero, zero_add]

def doubleUnit (A : GeneralLinear K n) : (Mat K n)ˣ where
  val := doubleMatrix K n A
  inv := doubleMatrix K n A⁻¹
  val_inv := by rw [← doubleMatrix_mul, mul_inv_cancel, doubleMatrix_one]
  inv_val := by rw [← doubleMatrix_mul, inv_mul_cancel, doubleMatrix_one]

def doubleHom : GeneralLinear K n →* (Mat K n)ˣ where
  toFun := doubleUnit K n
  map_one' := Units.ext (doubleMatrix_one K n)
  map_mul' A B := Units.ext (doubleMatrix_mul K n A B)

theorem doubleHom_preserves_form (A : GeneralLinear K n) :
    (doubleHom K n A).val * Matrix.J (Fin n) K *
      (doubleHom K n A).val.transpose = Matrix.J (Fin n) K := by
  have hA : A.val * (A⁻¹).val = 1 := Units.mul_inv A
  have ht : (A⁻¹).val.transpose * A.val.transpose = 1 := by
    rw [← Matrix.transpose_mul, hA, Matrix.transpose_one]
  change Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose * Matrix.J (Fin n) K *
    (Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose).transpose = Matrix.J (Fin n) K
  simp only [Matrix.J, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.transpose_transpose, Matrix.fromBlocks_multiply, mul_zero, zero_mul,
    add_zero, zero_add, mul_one, one_mul, Matrix.mul_neg, Matrix.neg_mul, hA, ht]

theorem doubleHom_mem (A : GeneralLinear K n) :
    doubleHom K n A ∈ elementaryRootGroup K n := by
  rw [CFSGSymplecticStabilizerCoordinates.elementaryRootGroup_eq_formPreserving K n]
  exact doubleHom_preserves_form K n A

def doubleIntoElementary : GeneralLinear K n →* elementaryRootGroup K n :=
  (doubleHom K n).codRestrict _ (doubleHom_mem K n)

theorem doubleIntoElementary_injective : Function.Injective (doubleIntoElementary K n) := by
  intro A B he
  have hv := congrArg (fun u : elementaryRootGroup K n =>
    Matrix.toBlocks₁₁ (u.val : Mat K n)) he
  change A.val = B.val at hv
  exact Units.ext hv

/-- Literal conjugation, before any quotient or action identification. -/
theorem doubleHom_upper_conjugation (A : GeneralLinear K n)
    (S : Matrix (Fin n) (Fin n) K) :
    doubleHom K n A * CFSGMatrixShearUnits.upper S * (doubleHom K n A)⁻¹ =
      CFSGMatrixShearUnits.upper (A.val * S * A.val.transpose) := by
  have hA : A.val * (A⁻¹).val = 1 := Units.mul_inv A
  have ht : (A⁻¹).val.transpose * A.val.transpose = 1 := by
    rw [← Matrix.transpose_mul, hA, Matrix.transpose_one]
  apply Units.ext
  change Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose *
    Matrix.fromBlocks 1 S 0 1 * Matrix.fromBlocks (A⁻¹).val 0 0 A.val.transpose =
      Matrix.fromBlocks 1 (A.val * S * A.val.transpose) 0 1
  simp only [Matrix.fromBlocks_multiply, mul_zero, zero_mul, add_zero,
    zero_add, mul_one, one_mul, hA, ht]

end SymmetricSubgroupAsymptotics.CFSGSymplecticGeneralLinearDouble
