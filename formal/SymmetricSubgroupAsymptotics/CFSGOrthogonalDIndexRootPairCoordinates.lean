import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements

/-! A chosen original basis of an original root plane expresses the
SAME original root displacement by a nonzero actual scalar. This is a
basis-change calculation, not a replacement group or action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPairOperator
open CFSGOrthogonalDIndexRootPlaneImage CFSGOrthogonalDIndexSingularRootPlanes
open CFSGOrthogonalDIndexPlaneRootLine CFSGOrthogonalDIndexFlagVectors
open CFSGOrthogonalDIndexBundledQuadratic CFSGAlternatingPairOperator
variable {K : Type} [Field K]

theorem root_displacement_of_spanning_pair (s : ℕ)
    (g : elementaryRootGroup K (s + 4)) (a : K) (ha : a ≠ 0)
    (u v : Index (s + 4) → K)
    (hspan : Submodule.span K {u, v} = conjugateRootPlane K s g) :
    ∃ c : K, c ≠ 0 ∧
      Matrix.mulVecLin (((g * highestRoot K s a * g⁻¹).val : Mat K (s + 4)) - 1) =
        c • pairOperator (splitQuadraticForm K (s + 4)).polarBilin u v := by
  have hp : (g.val : Mat K (s + 4)) *ᵥ firstVector K s ∈ Submodule.span K {u, v} := by
    rw [hspan]
    exact Submodule.subset_span (Or.inl rfl)
  have hq : (g.val : Mat K (s + 4)) *ᵥ secondVector K s ∈ Submodule.span K {u, v} := by
    rw [hspan]
    exact Submodule.subset_span (Or.inr rfl)
  obtain ⟨d, hd⟩ := pairOperator_mem_span (splitQuadraticForm K (s + 4)).polarBilin
    u v _ _ hp hq
  have hcoef : Matrix.mulVecLin
      (((g * highestRoot K s a * g⁻¹).val : Mat K (s + 4)) - 1) =
      (a * d) • pairOperator (splitQuadraticForm K (s + 4)).polarBilin u v := by
    rw [conjugate_highestRoot_displacement_pairOperator, hd, smul_smul]
  refine ⟨a * d, ?_, hcoef⟩
  intro hz
  have hzero : Matrix.mulVecLin
      (((g * highestRoot K s a * g⁻¹).val : Mat K (s + 4)) - 1) = 0 := by
    rw [hcoef, hz, zero_smul]
  have hr : conjugateRootPlane K s g = (⊥ : Submodule K (Index (s + 4) → K)) := by
    exact (conjugate_highestRoot_displacement_range K s g a ha).symm.trans
      ((congrArg LinearMap.range hzero).trans LinearMap.range_zero)
  have hh := congrArg (fun P : Submodule K (Index (s + 4) → K) => Module.finrank K P) hr
  change Module.finrank K (conjugateRootPlane K s g) =
    Module.finrank K (⊥ : Submodule K (Index (s + 4) → K)) at hh
  rw [conjugateRootPlane_finrank, finrank_bot] at hh
  omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
