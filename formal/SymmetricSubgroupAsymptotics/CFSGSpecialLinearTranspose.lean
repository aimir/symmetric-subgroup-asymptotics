import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! Literal inverse-transpose operations on determinant-one matrices. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGSpecialLinearTranspose
variable {K I : Type*} [CommRing K] [Fintype I] [DecidableEq I]

theorem transpose_transpose (A : Matrix.SpecialLinearGroup I K) :
    A.transpose.transpose = A := by
  apply Subtype.ext
  exact Matrix.transpose_transpose A.val

theorem transpose_inv (A : Matrix.SpecialLinearGroup I K) :
    (A⁻¹).transpose = (A.transpose)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change A.val.transpose * (A⁻¹).val.transpose = 1
  rw [← Matrix.transpose_mul]
  have h : (A⁻¹).val * A.val = 1 := congrArg Subtype.val (inv_mul_cancel A)
  rw [h, Matrix.transpose_one]

theorem inverseTranspose_twice (A : Matrix.SpecialLinearGroup I K) :
    (((A⁻¹).transpose)⁻¹).transpose = A := by
  have h : ((A⁻¹).transpose)⁻¹ = A.transpose := by rw [transpose_inv, inv_inv]
  rw [h]
  exact transpose_transpose A

end SymmetricSubgroupAsymptotics.CFSGSpecialLinearTranspose
