import SymmetricSubgroupAsymptotics.CFSGTwistedA2IntegralBasis

/-! The eight-vector basis after the ORIGINAL tensor base change.
This proves injectivity of the actual natural map in every characteristic
by an explicit two-sided coordinate inverse on the tensor product. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalRelations
open CFSG.Models.Chevalley CFSGTwistedANaturalMatrices
open CFSGTwistedA2MatrixCoordinates CFSGSerreSquareZeroMatrix
variable (K : Type) [Field K]

def fieldVectors (i : Fin 8) : Space A K := 1 ⊗ₜ[ℤ] integralVectors i

def fieldCombination : (Fin 8 → K) →ₗ[K] Space A K :=
  Fintype.linearCombination K (fieldVectors K)

def fieldCoordinates : Space A K →ₗ[K] (Fin 8 → K) :=
  (matrixCoordinates K).comp (baseChange (realizationData 2) K)

theorem baseChange_vectors (i : Fin 8) :
    baseChange (realizationData 2) K (fieldVectors K i) = matrixVectors K i := by
  rw [fieldVectors, baseChange_tmul, integralRepresentation_vectors, one_smul,
    map_matrixVectors]

theorem fieldCoordinates_vectors (i : Fin 8) :
    fieldCoordinates K (fieldVectors K i) = Pi.single i 1 := by
  change matrixCoordinates K (baseChange (realizationData 2) K (fieldVectors K i)) = _
  rw [baseChange_vectors, coordinates_vector]

theorem fieldCoordinates_combination (a : Fin 8 → K) :
    fieldCoordinates K (fieldCombination K a) = a := by
  classical
  change fieldCoordinates K (∑ i, a i • fieldVectors K i) = a
  rw [map_sum]
  simp only [map_smul, fieldCoordinates_vectors]
  funext j
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]

theorem fieldCombination_surjective : Function.Surjective (fieldCombination K) := by
  classical
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro x _
  induction x using TensorProduct.induction_on with
  | zero => exact (fieldCombination K).range.zero_mem
  | add x y hx hy => exact (fieldCombination K).range.add_mem (hx trivial) (hy trivial)
  | tmul a x =>
    have hv (i : Fin 8) : a ⊗ₜ[ℤ] integralVectors i ∈ (fieldCombination K).range := by
      rw [TensorProduct.tmul_eq_smul_one_tmul]
      apply (fieldCombination K).range.smul_mem a
      refine ⟨Pi.single i 1, ?_⟩
      exact (Fintype.linearCombination_apply_single K (fieldVectors K) i 1).trans
        (one_smul K (fieldVectors K i))
    rw [← integralCombination_coordinates x]
    change a ⊗ₜ[ℤ] (∑ i, integralCoordinates x i • integralVectors i) ∈ _
    rw [TensorProduct.tmul_sum]
    apply (fieldCombination K).range.sum_mem
    intro i _
    rw [TensorProduct.tmul_smul]
    exact (fieldCombination K).range.toAddSubgroup.zsmul_mem (hv i) _

theorem fieldCombination_coordinates (x : Space A K) :
    fieldCombination K (fieldCoordinates K x) = x := by
  obtain ⟨a, rfl⟩ := fieldCombination_surjective K x
  rw [fieldCoordinates_combination]

def fieldBasisEquiv : Space A K ≃ₗ[K] (Fin 8 → K) where
  __ := fieldCoordinates K
  invFun := fieldCombination K
  left_inv := fieldCombination_coordinates K
  right_inv := fieldCoordinates_combination K

theorem naturalBaseChange_injective :
    Function.Injective (baseChange (realizationData 2) K) := by
  intro x y h
  apply (fieldBasisEquiv K).injective
  exact congrArg (matrixCoordinates K) h

end SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalRelations
