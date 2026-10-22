import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSupport
import SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixUnits

/-! Exact diagonal-character transport by a matrix with a literal grading
permutation. This uses the original coordinate support, not coefficient-
field eigenvalue separation or recognition of a root operator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedDiagonalTransport
open CFSGGradedMatrixSupport CFSGDiagonalMatrixUnits
variable {I L K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

theorem matrix_mul_diagonal (weight : I→L) (e : L≃L) (d : L→K)
    (M : Matrix I I K) (hM : Supported weight e M) :
    M*Matrix.diagonal (fun i=>d (weight i))=
      Matrix.diagonal (fun i=>d (e.symm (weight i)))*M := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases he : weight i=e (weight j)
  · rw [he,e.symm_apply_apply]
    exact mul_comm _ _
  · rw [hM i j he,mul_zero,zero_mul]

theorem unit_mul_diagonal (weight : I→L) (e : L≃L) (d : L→Kˣ)
    (u : (Matrix I I K)ˣ) (hu : Supported weight e (u : Matrix I I K)) :
    u*diagonalHom I K (fun i=>d (weight i))=
      diagonalHom I K (fun i=>d (e.symm (weight i)))*u := by
  apply Units.ext
  exact matrix_mul_diagonal weight e (fun l=>(d l:K)) (u : Matrix I I K) hu

theorem unit_conjugate_diagonal (weight : I→L) (e : L≃L) (d : L→Kˣ)
    (u : (Matrix I I K)ˣ) (hu : Supported weight e (u : Matrix I I K)) :
    u*diagonalHom I K (fun i=>d (weight i))*u⁻¹=
      diagonalHom I K (fun i=>d (e.symm (weight i))) := by
  rw [unit_mul_diagonal weight e d u hu,mul_assoc,mul_inv_cancel,mul_one]

end SymmetricSubgroupAsymptotics.CFSGGradedDiagonalTransport
