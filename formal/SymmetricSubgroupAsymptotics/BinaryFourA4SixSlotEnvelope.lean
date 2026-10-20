import SymmetricSubgroupAsymptotics.BinaryFourCyclicEnvelopeCapacity
import SymmetricSubgroupAsymptotics.BinaryFourSymmetricEnvelopeAction
import SymmetricSubgroupAsymptotics.BinaryFourFullBlockQuotient

/-! The actual A4 common envelope has six slots. The extra S4 scalar
coordinate is absent; only the actual cyclic quotient acts on this space. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourFullBlockCoordinates BinaryFourSymmetricBlockActions

abbrev A4SixSpace := (Fin 2 → Scalar) × (Local × Local)

def a4SixCyclicRepresentation : Representation Scalar Ternary A4SixSpace :=
  (Representation.trivial Scalar Ternary (Fin 2 → Scalar)).prod
    (LinearSemidirectCoprimeSocleBounds.linearRepresentation doubleLinear)

def a4SixChart : (Middle × Local) ≃ₗ[Scalar] A4SixSpace where
  toFun x := (![middleChart x.1 0, middleChart x.1 1],
    ![middleChart x.1 2, middleChart x.1 3], x.2)
  invFun x := (middleChart.symm ![x.1 0, x.1 1, x.2.1 0, x.2.1 1], x.2.2)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by
    intro x y
    apply Prod.ext
    · ext i; fin_cases i <;> simp [map_add]
    · apply Prod.ext
      · ext i; fin_cases i <;> simp [map_add]
      · rfl
  map_smul' := by
    intro a x
    apply Prod.ext
    · ext i; fin_cases i <;> simp [map_smul]
    · apply Prod.ext
      · ext i; fin_cases i <;> simp [map_smul]
      · rfl

def a4SixCyclicEquiv : middleTopEnvelope.Equiv a4SixCyclicRepresentation where
  toLinearEquiv := a4SixChart
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    revert g x
    decide +kernel

theorem a4SixCyclic_uniform : UniformSubrepresentationGeneratorBound a4SixCyclicRepresentation 2 :=
  middleTopEnvelope_uniform.of_injective a4SixCyclicEquiv.symm.toIntertwiningMap
    a4SixCyclicEquiv.symm.injective

def a4SixInclusionLinear : A4SixSpace →ₗ[Scalar] SymmetricEnvelope where
  toFun x := (![x.1 0, x.1 1, 0], x.2)
  map_add' := by
    intro x y
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · rfl
  map_smul' := by
    intro a x
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · rfl

def a4SixProjectionLinear : SymmetricEnvelope →ₗ[Scalar] A4SixSpace where
  toFun x := (![x.1 0, x.1 1], x.2)
  map_add' := by
    intro x y
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · rfl
  map_smul' := by
    intro a x
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · rfl

def a4SixInclusion :
    Representation.IntertwiningMap
      (a4SixCyclicRepresentation.comp (SemidirectProduct.rightHom : Complement →* Ternary))
      (symmetricEnvelopeRepresentation.comp SemidirectProduct.inl) where
  toLinearMap := a4SixInclusionLinear
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    rcases g with ⟨p, z⟩
    revert p z x
    decide +kernel

def a4SixProjection :
    Representation.IntertwiningMap
      (symmetricEnvelopeRepresentation.comp (SemidirectProduct.inl : Complement →* SymmetricComplement))
      (a4SixCyclicRepresentation.comp SemidirectProduct.rightHom) where
  toLinearMap := a4SixProjectionLinear
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    rcases g with ⟨p, z⟩
    revert p z x
    decide +kernel

theorem a4SixInclusion_projection (x : SymmetricEnvelope) (hx : x.1 2 = 0) :
    a4SixInclusionLinear (a4SixProjectionLinear x) = x := by
  apply Prod.ext
  · ext i; fin_cases i <;> first | rfl | exact hx.symm
  · rfl

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
