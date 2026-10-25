import SymmetricSubgroupAsymptotics.CFSGTrialityBinaryTensorTranslationAction

/-! The literal fully raised tensor is a nonzero vector of the actual
fixed envelope, and all actual positive short parameters fix it. This
identifies the regular translation fixed line without a power-sum table. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityBinaryRaisedTensor
open CFSGTrialityMiddleFixedTensorSpan CFSGTrialityBinaryTensorTranslationAction
open CFSGTrialityGeckMiddleFixedTensorImage CFSGTrialityGeckMiddleTensorCovariance
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleCubeLinearEdges
open CFSGTrialityGeckMiddleCubeCoordinates CFSGTrialityGeckMiddleSignedTensorBasis
open CFSGTrialityGeckMiddleOrderedTensor CFSGTrialityGeckMiddleNormOrbitWords
open CFSGTrialityD4MiddleCube CFSGCubicTensorEnvelopeDimension
local instance trialityRaisedRootsDecidableEq :
    DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

def raised (q : CFSG.PrimePower) : fullEnvelope q := ⟨Pi.single 7 1,by
  apply mem_tensorEnvelope
  · simpa only [Pi.single_apply,show (7 : Fin 8)≠0 by decide,if_false] using
      (fixedScalarSpace q).zero_mem
  · simp only [Pi.single_eq_same]
    exact ⟨1,rfl⟩
  all_goals simp [Pi.single_apply]⟩

theorem raised_ne_zero (q : CFSG.PrimePower) : raised q≠0 := by
  intro h
  have he := congrArg (fun v : fullEnvelope q => v.val 7) h
  have hz : (1 : K q)=0 := by simpa only [raised,Pi.single_eq_same] using he
  exact one_ne_zero hz

theorem raised_embedding (q : CFSG.PrimePower) :
    fixedTensorEmbedding q (raised q)=actualTensor (K q) 7 := by
  change (∑ i : Fin 8, (Pi.single 7 (1 : K q) : Fin 8 → K q) i • actualTensor (K q) i)=_
  simp [Pi.single_apply]

private theorem outerLinear_raised (K : Type) [Field K] (i : Fin 3) (a : K) :
    outerLinear K i a (actualTensor K 7)=actualTensor K 7 := by
  rw [actualTensor,tensorWord_eq]
  obtain ⟨ε,_,he⟩ := tensorBasis_unit_sign (cubeBits 7)
  rw [he K,map_smul]
  exact congrArg (fun M : Mat K => (ε : K) • M)
    (one_bit_linear_fixed K (cubeBits 7) i (by fin_cases i <;> rfl) a)

private theorem normWord_raised (q : CFSG.PrimePower) (a : K q) :
    CFSGAlgebraConjugationAction.action (K q) (Mat (K q)) (normWord q a)
      (actualTensor (K q) 7)=actualTensor (K q) 7 := by
  simp only [normWord,orderedOuterWord,map_mul,LinearEquiv.mul_apply]
  change outerLinear (K q) 2 (a^(q.order^2))
    (outerLinear (K q) 1 (a^q.order) (outerLinear (K q) 0 a (actualTensor (K q) 7)))=_
  rw [outerLinear_raised,outerLinear_raised,outerLinear_raised]

theorem raised_translation_fixed (q : CFSG.PrimePower) (hq : q.order=2) (a : K q) :
    translationAction q hq (Multiplicative.ofAdd a) (raised q)=raised q := by
  apply fixedTensorEmbedding_injective q
  rw [translationAction_matrix,raised_embedding,←normWord_eq_shortOrbit]
  exact normWord_raised q a

end SymmetricSubgroupAsymptotics.CFSGTrialityBinaryRaisedTensor
