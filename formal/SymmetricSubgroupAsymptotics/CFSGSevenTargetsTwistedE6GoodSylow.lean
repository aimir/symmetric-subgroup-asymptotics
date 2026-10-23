import SymmetricSubgroupAsymptotics.CFSGSevenTargetsTrialityIndexSquare
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GoodSylowReduction

/-! T1 after the original twisted E6 good-Sylow proof, retaining the
completed original triality index square. Five published inputs, CFSG,
and two explicit narrowed model callbacks remain. This is not CFSG-only T1. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_five_published_inputs_cfsg_and_remaining_after_twistedE6_goodSylow
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterTwistedE6 i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterUnitaryOuter i →
        CFSGReduction.ModelBoundsAfterTrialityIndexSquare i) : T1 :=
  T1_of_five_published_inputs_cfsg_and_remaining_after_triality_index_square
    lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG
    (fun i _ _ hn _ => by
      rcases CFSGReduction.model_goodSylow_or_remaining_after_twistedE6 i hn with h | h
      · exact h
      · exact remainingGoodSylow i hn h)
    remainingSimpleIndex

theorem allTargets_of_five_published_inputs_cfsg_and_remaining_after_twistedE6_goodSylow
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterTwistedE6 i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterUnitaryOuter i →
        CFSGReduction.ModelBoundsAfterTrialityIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr (T1_of_five_published_inputs_cfsg_and_remaining_after_twistedE6_goodSylow
    lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
