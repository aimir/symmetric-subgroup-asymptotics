import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2RulingIntersection
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The actual column and row factor lines of a nonzero residual
rank-one matrix are its original linear-map ranges. These identities
will make the two maximal-extension coordinates unique. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
variable (K : Type) [Field K]

theorem outer_mulVec (u p x : Fin 2 → K) :
    columnMap K u p *ᵥ x = (p ⬝ᵥ x) • u := by
  funext i
  change (∑ j : Fin 2, (u i * p j) * x j) = (∑ j : Fin 2, p j * x j) * u i
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  ring

theorem outer_range (u p : Fin 2 → K) (hp : p ≠ 0) :
    LinearMap.range (Matrix.mulVecLin (columnMap K u p)) = Submodule.span K {u} := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [Matrix.mulVecLin_apply, outer_mulVec]
    exact (Submodule.span K {u}).smul_mem _ (Submodule.mem_span_singleton_self _)
  · apply Submodule.span_le.mpr
    rintro y rfl
    obtain ⟨j, hj⟩ := exists_factor_coordinate K p hp
    refine ⟨Pi.single j (p j)⁻¹, ?_⟩
    rw [Matrix.mulVecLin_apply, outer_mulVec, dotProduct_single, mul_inv_cancel₀ hj, one_smul]

theorem outer_transpose (u p : Fin 2 → K) : (columnMap K u p).transpose = columnMap K p u := by
  ext i j
  change u j * p i = p i * u j
  exact mul_comm _ _

theorem outer_transpose_range (u p : Fin 2 → K) (hu : u ≠ 0) :
    LinearMap.range (Matrix.mulVecLin (columnMap K u p).transpose) = Submodule.span K {p} := by
  rw [outer_transpose]
  exact outer_range K p u hu

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
