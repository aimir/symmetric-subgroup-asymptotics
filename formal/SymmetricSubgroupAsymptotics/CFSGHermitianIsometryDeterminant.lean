import SymmetricSubgroupAsymptotics.CFSGHermitianMatrixPullback
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Determinants of the literal Hermitian isometries have norm one.
This is extracted from the actual matrix equation, with no published
unitary order or determinant-image formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGHermitianIsometryDeterminant
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem determinant_norm_one (sigma : K ≃+* K) (H A : (Matrix I I K)ˣ)
    (hA : ∀ v w, hermitianPair sigma H ((A : Matrix I I K) *ᵥ v)
      ((A : Matrix I I K) *ᵥ w) = hermitianPair sigma H v w) :
    sigma (Matrix.det (A : Matrix I I K)) * Matrix.det (A : Matrix I I K) = 1 := by
  have hm := (CFSGHermitianMatrixPullback.similitude_matrix_iff (I := I) sigma
    (H : Matrix I I K) (A : Matrix I I K) (1 : K)).mp
    (by simpa only [one_mul] using hA)
  rw [one_smul] at hm
  have hd := congrArg Matrix.det hm
  have hmap : Matrix.det ((A : Matrix I I K).map sigma) = sigma (Matrix.det (A : Matrix I I K)) :=
    (RingHom.map_det sigma.toRingHom (A : Matrix I I K)).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hmap] at hd
  have hH : Matrix.det (H : Matrix I I K) ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero H
  apply mul_right_cancel₀ hH
  calc
    (sigma (Matrix.det (A : Matrix I I K)) * Matrix.det (A : Matrix I I K)) *
        Matrix.det (H : Matrix I I K) =
      sigma (Matrix.det (A : Matrix I I K)) * Matrix.det (H : Matrix I I K) *
        Matrix.det (A : Matrix I I K) := by ring
    _ = Matrix.det (H : Matrix I I K) := hd
    _ = 1 * Matrix.det (H : Matrix I I K) := (one_mul _).symm

end SymmetricSubgroupAsymptotics.CFSGHermitianIsometryDeterminant
