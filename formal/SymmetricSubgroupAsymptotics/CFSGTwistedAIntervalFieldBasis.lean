import SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalIntegralBasis

/-! The actual interval basis after the ORIGINAL integral tensor base
change, every rank and characteristic. The explicit two-sided coordinate
inverse proves faithful natural base change; rational injectivity alone
is not used as a reduction-modulo-p argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
open CFSG.Models.Chevalley CFSGTwistedANaturalMatrices
open CFSGTwistedAIntervalMatrixCoordinates CFSGSerreSquareZeroMatrix
variable (K : Type) [Field K] (r : ℕ)

def fieldVectors (i : BasisIndex r) : Space (CartanMatrix.A r) K := 1 ⊗ₜ[ℤ] integralVectors r i

def fieldCombination : (BasisIndex r → K) →ₗ[K] Space (CartanMatrix.A r) K :=
  Fintype.linearCombination K (fieldVectors K r)

def fieldCoordinates : Space (CartanMatrix.A r) K →ₗ[K] (BasisIndex r → K) :=
  (matrixCoordinates K r).comp (baseChange (realizationData r) K)

theorem baseChange_vectors (i : BasisIndex r) :
    baseChange (realizationData r) K (fieldVectors K r i) = matrixVectors K r i := by
  rw [fieldVectors, baseChange_tmul, integralRepresentation_vectors, one_smul,
    map_matrixVectors]

theorem fieldCoordinates_vectors (i : BasisIndex r) :
    fieldCoordinates K r (fieldVectors K r i) = Pi.single i 1 := by
  change matrixCoordinates K r (baseChange (realizationData r) K (fieldVectors K r i)) = _
  rw [baseChange_vectors, coordinates_vector]

theorem fieldCoordinates_combination (a : BasisIndex r → K) :
    fieldCoordinates K r (fieldCombination K r a) = a := by
  classical
  change fieldCoordinates K r (∑ i, a i • fieldVectors K r i) = a
  rw [map_sum]
  simp only [map_smul, fieldCoordinates_vectors]
  funext j
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]

theorem fieldCombination_surjective : Function.Surjective (fieldCombination K r) := by
  classical
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro x _
  induction x using TensorProduct.induction_on with
  | zero => exact (fieldCombination K r).range.zero_mem
  | add x y hx hy => exact (fieldCombination K r).range.add_mem (hx trivial) (hy trivial)
  | tmul a x =>
    have hv (i : BasisIndex r) : a ⊗ₜ[ℤ] integralVectors r i ∈ (fieldCombination K r).range := by
      rw [TensorProduct.tmul_eq_smul_one_tmul]
      apply (fieldCombination K r).range.smul_mem a
      refine ⟨Pi.single i 1, ?_⟩
      exact (Fintype.linearCombination_apply_single K (fieldVectors K r) i 1).trans
        (one_smul K (fieldVectors K r i))
    rw [← integralCombination_coordinates r x]
    change a ⊗ₜ[ℤ] (∑ i, integralCoordinates r x i • integralVectors r i) ∈ _
    rw [TensorProduct.tmul_sum]
    apply (fieldCombination K r).range.sum_mem
    intro i _
    rw [TensorProduct.tmul_smul]
    exact (fieldCombination K r).range.toAddSubgroup.zsmul_mem (hv i) _

theorem fieldCombination_coordinates (x : Space (CartanMatrix.A r) K) :
    fieldCombination K r (fieldCoordinates K r x) = x := by
  obtain ⟨a, rfl⟩ := fieldCombination_surjective K r x
  rw [fieldCoordinates_combination]

def fieldBasisEquiv : Space (CartanMatrix.A r) K ≃ₗ[K] (BasisIndex r → K) where
  __ := fieldCoordinates K r
  invFun := fieldCombination K r
  left_inv := fieldCombination_coordinates K r
  right_inv := fieldCoordinates_combination K r

theorem naturalBaseChange_injective :
    Function.Injective (baseChange (realizationData r) K) := by
  intro x y h
  apply (fieldBasisEquiv K r).injective
  exact congrArg (matrixCoordinates K r) h

end SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
