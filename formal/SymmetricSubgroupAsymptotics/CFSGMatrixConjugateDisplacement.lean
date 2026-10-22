import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Exact displacement-image transport under the SAME literal matrix
conjugator. No characteristic, form or group-identification premise. -/
set_option autoImplicit false
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGMatrixConjugateDisplacement
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem conjugate_sub_one (g h : (Matrix I I K)ˣ) :
    ((g * h * g⁻¹ : (Matrix I I K)ˣ) : Matrix I I K) - 1 =
      (g : Matrix I I K) * ((h : Matrix I I K) - 1) * (↑(g⁻¹) : Matrix I I K) := by
  change (g : Matrix I I K) * (h : Matrix I I K) * (↑(g⁻¹) : Matrix I I K) - 1 = _
  rw [mul_sub, sub_mul, mul_one, Units.mul_inv]

theorem conjugate_range (g : (Matrix I I K)ˣ) (A : Matrix I I K) :
    LinearMap.range (Matrix.mulVecLin ((g : Matrix I I K) * A * (↑(g⁻¹) : Matrix I I K))) =
      (LinearMap.range (Matrix.mulVecLin A)).map (Matrix.mulVecLin (g : Matrix I I K)) := by
  have hs : Function.Surjective (Matrix.mulVecLin (↑(g⁻¹) : Matrix I I K)) := by
    intro v
    refine ⟨(g : Matrix I I K) *ᵥ v, ?_⟩
    change (↑(g⁻¹) : Matrix I I K) *ᵥ ((g : Matrix I I K) *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp, LinearMap.range_eq_top.mpr hs,
    Submodule.map_top, Matrix.mulVecLin_mul, LinearMap.range_comp]

end SymmetricSubgroupAsymptotics.CFSGMatrixConjugateDisplacement
