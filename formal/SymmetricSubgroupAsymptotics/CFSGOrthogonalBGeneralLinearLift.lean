import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexShears
import SymmetricSubgroupAsymptotics.CFSGGeneralLinearDeterminantCosets

/-! Literal GL block lifts in the original odd-orthogonal natural space.
Their determinant-one parameter subgroup lies in the SAME elementary B
group by the checked original adjacent-root SL generation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGeneralLinearLift
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationSLChain
open CFSGMatrixDiagonalBlockLift CFSGOrthogonalBIndexShears
variable (K : Type) [Field K]

def generalLinearLift (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) K →* (Mat K n)ˣ :=
  (extensionHom K n).comp lift

theorem generalLinearLift_val (n : ℕ) (A : Matrix.GeneralLinearGroup (Fin n) K) :
    (generalLinearLift K n A : Mat K n) = Matrix.fromBlocks
      (Matrix.fromBlocks (A : Matrix (Fin n) (Fin n) K) 0 0
        ((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose)
      0 0 1 := rfl

theorem generalLinearLift_special (n : ℕ) (S : Matrix.SpecialLinearGroup (Fin n) K) :
    generalLinearLift K n S.toGL = (doubleIntoElementary K n S).val := by
  apply Units.ext
  rw [generalLinearLift_val]
  change Matrix.fromBlocks (Matrix.fromBlocks S.val 0 0
      ((S.toGL⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose)
      0 0 1 = Matrix.fromBlocks (Matrix.fromBlocks S.val 0 0 (S⁻¹).val.transpose) 0 0 1
  have hi : ((S.toGL⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (S⁻¹).val := by
    exact congrArg (fun A : Matrix.GeneralLinearGroup (Fin n) K =>
      (A : Matrix (Fin n) (Fin n) K)) (map_inv Matrix.SpecialLinearGroup.toGL S).symm
  rw [hi]

theorem generalLinearLift_special_mem (n : ℕ) (S : Matrix.SpecialLinearGroup (Fin n) K) :
    generalLinearLift K n S.toGL ∈ elementaryRootGroup K n := by
  rw [generalLinearLift_special]
  exact (doubleIntoElementary K n S).property

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
    _ = _ := by rw [map_mul, generalLinearLift_special]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGeneralLinearLift
