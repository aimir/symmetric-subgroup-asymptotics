import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSLDouble
import SymmetricSubgroupAsymptotics.CFSGMatrixDiagonalBlockLift
import SymmetricSubgroupAsymptotics.CFSGGeneralLinearDeterminantCosets
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticForm

/-! Actual paired GL lifts preserve the split quadratic form in every
characteristic. Their determinant-one part lies in the SAME original
elementary D group, and their remaining parameter is the actual GL
determinant. No full isometry-group identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexGeneralLinearLift
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble
open CFSGMatrixDiagonalBlockLift CFSGOrthogonalDIndexQuadraticForm
variable (K : Type) [Field K]

abbrev generalLinearLift (r : ℕ) : Matrix.GeneralLinearGroup (Fin r) K →* (Mat K r)ˣ := lift

theorem generalLinearLift_val (r : ℕ) (A : Matrix.GeneralLinearGroup (Fin r) K) :
    (generalLinearLift K r A : Mat K r) = Matrix.fromBlocks
      (A : Matrix (Fin r) (Fin r) K) 0 0
      ((A⁻¹ : Matrix.GeneralLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K).transpose := rfl

theorem generalLinearLift_preserves (r : ℕ) (A : Matrix.GeneralLinearGroup (Fin r) K) :
    generalLinearLift K r A ∈ quadraticPreserving K r := by
  intro x
  rw [generalLinearLift_val, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, zero_add, add_zero]
  change ((A : Matrix (Fin r) (Fin r) K) *ᵥ leftPart K x) ⬝ᵥ
      (((A⁻¹ : Matrix.GeneralLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K).transpose *ᵥ
        rightPart K x) = leftPart K x ⬝ᵥ rightPart K x
  rw [dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
    Units.inv_mul, Matrix.one_mulVec]

theorem generalLinearLift_special (r : ℕ) (S : Matrix.SpecialLinearGroup (Fin r) K) :
    generalLinearLift K r S.toGL = doubleHom K r S := by
  apply Units.ext
  rw [generalLinearLift_val]
  change Matrix.fromBlocks S.val 0 0
      ((S.toGL⁻¹ : Matrix.GeneralLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K).transpose =
    Matrix.fromBlocks S.val 0 0 (S⁻¹).val.transpose
  have hi : ((S.toGL⁻¹ : Matrix.GeneralLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K) =
      (S⁻¹).val := by
    exact congrArg (fun A : Matrix.GeneralLinearGroup (Fin r) K =>
      (A : Matrix (Fin r) (Fin r) K)) (map_inv Matrix.SpecialLinearGroup.toGL S).symm
  rw [hi]

theorem generalLinearLift_special_mem (r : ℕ) (S : Matrix.SpecialLinearGroup (Fin r) K) :
    generalLinearLift K r S.toGL ∈ elementaryRootGroup K r := by
  rw [generalLinearLift_special]
  exact doubleHom_range_le K r ⟨S, rfl⟩

theorem generalLinearLift_factor (s : ℕ) (A : Matrix.GeneralLinearGroup (Fin (s + 1)) K) :
    ∃ e : elementaryRootGroup K (s + 1), generalLinearLift K (s + 1) A =
      generalLinearLift K (s + 1)
        (CFSGGeneralLinearDeterminantCosets.lastDiagonal K s (Matrix.GeneralLinearGroup.det A)) * e.val := by
  obtain ⟨S, hS⟩ := CFSGGeneralLinearDeterminantCosets.exists_special_factor K s A
  refine ⟨doubleIntoElementary K (s + 1) S, ?_⟩
  calc
    generalLinearLift K (s + 1) A = generalLinearLift K (s + 1)
        (CFSGGeneralLinearDeterminantCosets.lastDiagonal K s (Matrix.GeneralLinearGroup.det A) * S.toGL) :=
      congrArg (generalLinearLift K (s + 1)) hS
    _ = _ := by
      rw [map_mul, generalLinearLift_special]
      rfl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexGeneralLinearLift
