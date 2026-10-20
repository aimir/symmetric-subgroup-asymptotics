import SymmetricSubgroupAsymptotics.BinaryFourSymmetricEnvelopeComponentActions
import SymmetricSubgroupAsymptotics.BinaryFourSymmetricEnvelopeSubspaceSplit

/-! Exact component chart for the retained S4 envelope. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourSymmetricBlockActions

def symmetricEnvelopeComponentChart : symmetricEnvelopeRepresentation.Equiv
    (trivialEnvelopeRepresentation.prod activeEnvelopeRepresentation) where
  toLinearEquiv := LinearEquiv.refl Scalar SymmetricEnvelope
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    rcases g with ⟨⟨p, z⟩, b⟩
    revert p z b x
    decide +kernel

def symmetricEnvelopeTrivialProjection : symmetricEnvelopeRepresentation.IntertwiningMap
    trivialEnvelopeRepresentation where
  toLinearMap := LinearMap.fst Scalar (Fin 3 → Scalar) (Local × Local)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have h := Representation.IntertwiningMap.isIntertwining _ _
      symmetricEnvelopeComponentChart.toIntertwiningMap g x
    exact congrArg Prod.fst h

def symmetricEnvelopeActiveProjection : symmetricEnvelopeRepresentation.IntertwiningMap
    activeEnvelopeRepresentation where
  toLinearMap := LinearMap.snd Scalar (Fin 3 → Scalar) (Local × Local)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have h := Representation.IntertwiningMap.isIntertwining _ _
      symmetricEnvelopeComponentChart.toIntertwiningMap g x
    exact congrArg Prod.snd h

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
