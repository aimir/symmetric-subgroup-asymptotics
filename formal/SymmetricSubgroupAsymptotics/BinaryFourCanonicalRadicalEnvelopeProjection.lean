import SymmetricSubgroupAsymptotics.BinaryFourSymmetricEnvelopeCapacity
import SymmetricSubgroupAsymptotics.BinaryFourCanonicalSymmetricInducedChart

/-! The actual middle-coordinate map from the canonical radical into
its four occupied positions in the seven-dimensional common envelope.
Equivariance checks only six basis vectors of the original radical. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourFullBlockCoordinates BinaryFourSymmetricBlockActions

def fullHeadLinear : FullCoordinates →ₗ[Scalar] Coordinates where
  toFun := head
  map_add' := by intro x y; ext i; fin_cases i <;> rfl
  map_smul' := by intro a x; ext i; fin_cases i <;> rfl

def includeAugmentationLinear : Coordinates →ₗ[Scalar] FullCoordinates where
  toFun := includeAugmentation
  map_add' := by intro x y; ext i; fin_cases i <;> rfl
  map_smul' := by intro a x; ext i; fin_cases i <;> rfl

def middleEnvelopeInclusion : Middle →ₗ[Scalar] SymmetricEnvelope where
  toFun x := (![x 0, x 1, 0], ![x 2, x 3], 0)
  map_add' := by
    intro x y
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · apply Prod.ext
      · ext i; fin_cases i <;> rfl
      · rfl
  map_smul' := by
    intro a x
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · apply Prod.ext
      · ext i; fin_cases i <;> rfl
      · rfl

def radicalEnvelopeProjection : FullCoordinates →ₗ[Scalar] SymmetricEnvelope :=
  middleEnvelopeInclusion.comp (middleChart.toLinearMap.comp
    (middleProjection.comp fullHeadLinear))

theorem radicalEnvelopeProjection_intertwining_on_radical
    (g : SymmetricComplement) :
    radicalEnvelopeProjection.comp
        ((BinaryFourCanonicalSymmetricInducedChart.fullCoordinatesRepresentation g).comp
          includeAugmentationLinear) =
      (symmetricEnvelopeRepresentation g).comp
        (radicalEnvelopeProjection.comp includeAugmentationLinear) := by
  apply (Pi.basisFun Scalar (Fin 6)).ext
  intro i
  rw [Pi.basisFun_apply]
  rcases g with ⟨⟨p, z⟩, b⟩
  revert p z b i
  decide +kernel

theorem radicalEnvelopeProjection_kernel (x : Coordinates) :
    radicalEnvelopeProjection (includeAugmentation x) = 0 ↔
      middleProjection x = 0 := by
  revert x
  decide +kernel

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
