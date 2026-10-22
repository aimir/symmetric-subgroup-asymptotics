import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGeneralLinearLift
import SymmetricSubgroupAsymptotics.CFSGHyperbolicTriangularDeterminant
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUpperShearForm
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSpecialFormGroup

/-! Every actual GL paired-block lift is a determinant-one isometry of
the original B Gram matrix. No elementary membership is claimed for a
general GL parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGeneralLinearForm
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGeneralLinearLift
open CFSGMatrixDiagonalBlockLift CFSGOrthogonalBSpecialFormGroup
variable (K : Type) [Field K]

theorem paired_lift_preserves (n : ℕ) (A : Matrix.GeneralLinearGroup (Fin n) K) :
    (lift A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).transpose *
      CFSGHyperbolicTriangularDeterminant.hyperbolicGram *
      (lift A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        CFSGHyperbolicTriangularDeterminant.hyperbolicGram := by
  have hLR : (A : Matrix (Fin n) (Fin n) K).transpose *
      ((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose = 1 := by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  have hLR' := hLR
  rw [Matrix.GeneralLinearGroup.coe_inv] at hLR'
  simp [lift, CFSGHyperbolicTriangularDeterminant.hyperbolicGram,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hLR']

theorem generalLinearLift_preserves (n : ℕ) (A : Matrix.GeneralLinearGroup (Fin n) K) :
    (generalLinearLift K n A : Mat K n).transpose * gram K n *
      (generalLinearLift K n A : Mat K n) = gram K n := by
  have hp := paired_lift_preserves K n A
  change (Matrix.fromBlocks (lift A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) 0 0 1).transpose *
      gram K n * Matrix.fromBlocks (lift A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) 0 0 1 = _
  rw [CFSGOrthogonalBUnipotent.gram_blocks]
  simp only [Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_one,
    Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    mul_one]
  exact congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K =>
    Matrix.fromBlocks M 0 0 (1 : Matrix Unit Unit K)) hp

theorem generalLinearLift_det (n : ℕ) (A : Matrix.GeneralLinearGroup (Fin n) K) :
    (generalLinearLift K n A : Mat K n).det = 1 := by
  rw [generalLinearLift_val, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose, ← Matrix.det_mul,
    Units.mul_inv, Matrix.det_one]

theorem generalLinearLift_mem_special (n : ℕ) (A : Matrix.GeneralLinearGroup (Fin n) K) :
    generalLinearLift K n A ∈ specialFormUnits K n :=
  (mem_specialFormUnits_iff K n _).mpr
    ⟨generalLinearLift_preserves K n A, generalLinearLift_det K n A⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGeneralLinearForm
