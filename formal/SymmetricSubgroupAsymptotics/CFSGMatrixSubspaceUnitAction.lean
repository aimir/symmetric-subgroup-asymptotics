import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Literal unit matrices act on actual submodules by their natural
linear maps. Invariance passes to the inverse without quotienting or
replacing the submodule. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMatrixSubspaceUnitAction
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem map_mul (P : Submodule K (I → K)) (g h : (Matrix I I K)ˣ) :
    P.map (Matrix.mulVecLin ((g * h : (Matrix I I K)ˣ) : Matrix I I K)) =
      (P.map (Matrix.mulVecLin (h : Matrix I I K))).map
        (Matrix.mulVecLin (g : Matrix I I K)) := by
  rw [Units.val_mul, Matrix.mulVecLin_mul, Submodule.map_comp]

theorem map_one (P : Submodule K (I → K)) :
    P.map (Matrix.mulVecLin (1 : Matrix I I K)) = P := by
  rw [Matrix.mulVecLin_one, Submodule.map_id]

theorem invariant_inverse (P : Submodule K (I → K)) (g : (Matrix I I K)ˣ)
    (hg : P.map (Matrix.mulVecLin (g : Matrix I I K)) = P) :
    P.map (Matrix.mulVecLin ((g⁻¹ : (Matrix I I K)ˣ) : Matrix I I K)) = P := by
  calc
    P.map (Matrix.mulVecLin ((g⁻¹ : (Matrix I I K)ˣ) : Matrix I I K)) =
        (P.map (Matrix.mulVecLin (g : Matrix I I K))).map
          (Matrix.mulVecLin ((g⁻¹ : (Matrix I I K)ˣ) : Matrix I I K)) := by rw [hg]
    _ = P.map (Matrix.mulVecLin ((g⁻¹ * g : (Matrix I I K)ˣ) : Matrix I I K)) := (map_mul P g⁻¹ g).symm
    _ = P := by rw [inv_mul_cancel, Units.val_one, map_one]

end SymmetricSubgroupAsymptotics.CFSGMatrixSubspaceUnitAction
