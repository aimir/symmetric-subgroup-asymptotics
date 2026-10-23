import SymmetricSubgroupAsymptotics.CFSGSevenTargetsFFour
import SymmetricSubgroupAsymptotics.CFSGTwistedDCompleteSufficientSimpleIndex

/-! The original nonsplit D branch is absent from BOTH model residuals.
The previous F4/triality good-Sylow closures are retained. Five published
inputs and two strictly stated remaining model callbacks still remain;
this is not a CFSG-only theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_five_published_inputs_cfsg_and_remaining_after_twistedD_outer
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterFFour i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterTwistedDOuter i →
        CFSGReduction.ModelBoundsAfterTwistedDSquare i) : T1 :=
  T1_of_five_published_inputs_cfsg_and_remaining_after_fFour
    lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow
    (fun i _ _ hn hi => CFSGReduction.modelBoundsAfterTwistedDSquare_of_remaining_after_twistedD_outer
      i hn hi (remainingSimpleIndex i hn))

theorem allTargets_of_five_published_inputs_cfsg_and_remaining_after_twistedD_outer
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterFFour i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterTwistedDOuter i →
        CFSGReduction.ModelBoundsAfterTwistedDSquare i) : AllTargets :=
  allTargets_iff_T1.mpr (T1_of_five_published_inputs_cfsg_and_remaining_after_twistedD_outer
    lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
