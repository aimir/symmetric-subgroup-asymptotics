import SymmetricSubgroupAsymptotics.CFSGTrialityMiddleFixedTensorSpan
import SymmetricSubgroupAsymptotics.CFSGCubicTensorEnvelopeCoordinates

/-! Exact dimension and order of the actual Frobenius-fixed tensor
envelope. This is a statement about its already-proved scalar coordinates;
the independent fixed-word lift and kernel theorems supply the eventual
radical quotient identification. No fixed-point lifting is presumed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityMiddleFixedTensorCardinality

open CFSGTrialityFixedField CFSGTrialityMiddleFixedTensorSpan
open CFSGCubicTensorEnvelopeCoordinates

def fixedScalarEquiv (q : CFSG.PrimePower) : F q ≃ₗ[F q] fixedScalarSpace q :=
  LinearEquiv.ofInjective (Algebra.linearMap (F q) (K q))
    (fun _a _b hab => Subtype.ext hab)

theorem fullEnvelope_finrank (q : CFSG.PrimePower) :
    Module.finrank (F q) (fullEnvelope q) = 8 := by
  change Module.finrank (F q)
    (CFSGCubicTensorEnvelopeDimension.tensorEnvelope (fixedScalarSpace q) (sigmaLinear q)) = 8
  rw [tensorEnvelope_finrank, ← (fixedScalarEquiv q).finrank_eq,
    Module.finrank_self, extension_finrank]

theorem fullEnvelope_card (q : CFSG.PrimePower) : Nat.card (fullEnvelope q) = q.order ^ 8 := by
  change Nat.card
    (CFSGCubicTensorEnvelopeDimension.tensorEnvelope (fixedScalarSpace q) (sigmaLinear q)) = _
  rw [tensorEnvelope_card, ← Nat.card_congr (fixedScalarEquiv q).toEquiv,
    fixedField_card, CFSGTrialityTripleFixedRoots.extension_three_card]
  ring

end SymmetricSubgroupAsymptotics.CFSGTrialityMiddleFixedTensorCardinality
