import SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleAutomorphismAction
import SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleNormalizer
import SymmetricSubgroupAsymptotics.CFSGTrialityBinaryTensorTranslationAction
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixBlockProjection

/-! The canonical quotient action of the actual generated normalizer
agrees with literal matrix conjugation for degree-preserving elements.
Its displayed positive parameters are exactly the proved regular
translation action on the eight actual norm-curve basis vectors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleVectorAction
open CFSGTrialityMiddleFixedTensorSpan CFSGTrialityBinaryMiddleNormalizer
open CFSGTrialityGeckMiddleFixedCommutators CFSGTrialityGeckMiddleFixedQuotientCoordinates
open CFSGTrialityGeckMiddleFixedTensorImage CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleNormOrbitWords CFSGTrialityGeckMiddleOrderedTensor
open CFSGTrialityGeckMiddleCubeLinearEdges CFSGGradedMatrixSubgroups
open CFSGTrialityBinaryTensorTranslationAction CFSGTrialityGeckFixedRootWords
local instance trialityMiddleVectorActionRootsDecidableEq :
    DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

def vectorAction (q : CFSG.PrimePower) (hq : q.order=2) :
    carrier q →* (fullEnvelope q ≃ₗ[F q] fullEnvelope q) :=
  (CFSGTrialityBinaryMiddleAutomorphismAction.linearAction q hq).comp (conjugationAction q)

theorem vectorAction_coordinate (q : CFSG.PrimePower) (hq : q.order=2)
    (g : carrier q) (u : fixedMiddle q) :
    vectorAction q hq g (coordinate q u)=coordinate q (conjugationAction q g u) :=
  CFSGTrialityBinaryMiddleAutomorphismAction.linearAction_coordinate q hq _ u

theorem vectorAction_matrix (q : CFSG.PrimePower) (hq : q.order=2)
    (g : carrier q) (hg : g.val ∈ preservingUnits middleWeight) (c : fullEnvelope q) :
    fixedTensorEmbedding q (vectorAction q hq g c)=
      CFSGAlgebraConjugationAction.action (K q) (Mat (K q)) g.val
        (fixedTensorEmbedding q c) := by
  obtain ⟨u,hu⟩ := projection_surjective q (Multiplicative.ofAdd c)
  have hc : coordinate q u=c := congrArg (fun z : Multiplicative (fullEnvelope q) => z.toAdd) hu
  calc
    _ = CFSGGradedMatrixGroupFirstLayer.firstLayer middleWeight
        (conjugationAction q g u).val := by
      rw [←hc,vectorAction_coordinate,coordinate_spec]
    _ = g.val.val * CFSGGradedMatrixGroupFirstLayer.firstLayer middleWeight u.val *
        (g.val⁻¹).val := by
      rw [conjugationAction_val]
      exact CFSGGradedMatrixBlockProjection.firstLayer_conjugate
        (K q) middleWeight g.val u.val hg ((preservingUnits middleWeight).inv_mem hg)
    _ = _ := by rw [←coordinate_spec q u,hc]; rfl

private theorem positive_preserving (q : CFSG.PrimePower) (a : K q) :
    normWord q a ∈ preservingUnits middleWeight :=
  (preservingUnits middleWeight).mul_mem (outerWord_preserving _ 2 _)
    ((preservingUnits middleWeight).mul_mem (outerWord_preserving _ 1 _)
      (outerWord_preserving _ 0 _))

theorem positive_vectorAction (q : CFSG.PrimePower) (hq : q.order=2) (a : K q) :
    vectorAction q hq (positiveElement q a)=
      translationAction q hq (Multiplicative.ofAdd a) := by
  apply LinearEquiv.ext
  intro c
  apply fixedTensorEmbedding_injective q
  calc
    _ = CFSGAlgebraConjugationAction.action (K q) (Mat (K q)) (normWord q a)
        (fixedTensorEmbedding q c) :=
      vectorAction_matrix q hq (positiveElement q a) (positive_preserving q a) c
    _ = _ := by
      rw [normWord_eq_shortOrbit]
      exact (translationAction_matrix q hq a c).symm

end SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleVectorAction
