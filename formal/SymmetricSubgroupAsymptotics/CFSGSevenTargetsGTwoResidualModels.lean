import SymmetricSubgroupAsymptotics.CFSGSufficientPublishedTargetsOrder
import SymmetricSubgroupAsymptotics.CFSGGTwoGoodSylowReduction

/-! The current model reductions are threaded into the actual T1/AllTargets
consumer. Five published inputs and TWO genuine remaining model obligations
are explicit. This is a residual interface, not a CFSG-only endpoint. The
alternating, untwisted classical, Suzuki, exceptional E, G2 and rank-two twisted-A
GoodSylow cases are discharged by proved original-model witnesses. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_five_published_inputs_cfsg_and_remaining_models_after_G2
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model →
        CFSGReduction.RemainingGoodSylowIndexWithoutClassicalSuzukiEAlternatingTwistedA2AndG2 i →
          ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexModelWithoutClassicalSuzuki i →
          CFSGReduction.ModelSufficientSimpleIndexBounds i) : T1 :=
  T1_of_six_published_inputs_cfsg_and_remaining_nonclassical_simpleIndex
    lit (CFSGReduction.aschbacherGuralnick_of_cfsg_and_remaining_without_classical_suzuki_E_alternating_twistedA2_G2
      hCFSG remainingGoodSylow)
    hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingSimpleIndex

theorem allTargets_of_five_published_inputs_cfsg_and_remaining_models_after_G2
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model →
        CFSGReduction.RemainingGoodSylowIndexWithoutClassicalSuzukiEAlternatingTwistedA2AndG2 i →
          ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexModelWithoutClassicalSuzuki i →
          CFSGReduction.ModelSufficientSimpleIndexBounds i) : AllTargets :=
  allTargets_iff_T1.mpr (T1_of_five_published_inputs_cfsg_and_remaining_models_after_G2
    lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
