import SymmetricSubgroupAsymptotics.BinaryFourCanonicalRadicalEnvelopeProjection

/-! The bottom and augmentation-top binary plane embeds in the middle's
active plane. The explicit basis change is localCycle.symm, retaining the
canonical odd reflection as well as the ternary action. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourSymmetricBlockActions

def canonicalLocalRepresentation : Representation Scalar SymmetricComplement Local :=
  LinearSemidirectCoprimeSocleBounds.linearRepresentation
    BinaryFourCanonicalSymmetricInducedChart.localLinear

def localMiddleInclusionLinear : Local →ₗ[Scalar] SymmetricEnvelope where
  toFun a := (0, localCycle.symm a, 0)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · exact Prod.ext (map_add localCycle.symm x y) rfl
  map_smul' a x := by
    apply Prod.ext
    · rfl
    · exact Prod.ext (map_smul localCycle.symm a x) rfl

def canonicalLocalMiddleInclusion : canonicalLocalRepresentation.IntertwiningMap
    symmetricEnvelopeRepresentation where
  toLinearMap := localMiddleInclusionLinear
  isIntertwining' g := by
    apply (Pi.basisFun Scalar (Fin 2)).ext
    intro i
    rw [Pi.basisFun_apply]
    rcases g with ⟨⟨p, z⟩, b⟩
    revert p z b i
    decide +kernel

theorem canonicalLocalMiddleInclusion_injective :
    Function.Injective canonicalLocalMiddleInclusion := by
  intro a b h
  apply localCycle.symm.injective
  exact congrArg (fun x : SymmetricEnvelope => x.2.1) h

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
