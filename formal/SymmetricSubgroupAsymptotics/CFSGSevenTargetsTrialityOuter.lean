import SymmetricSubgroupAsymptotics.CFSGSevenTargetsTwistedE6Outer
import SymmetricSubgroupAsymptotics.CFSGTrialityCompleteSufficientSimpleIndex

/-! T1 with ORIGINAL triality and twisted E6 discharged from both model
callbacks. Five published inputs, CFSG and two smaller explicit model
callbacks remain; this statement is not a CFSG-only T1 theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_five_published_inputs_cfsg_and_remaining_after_triality_outer
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
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterTrialityOuter i →
        CFSGReduction.ModelBoundsAfterFFourTwistedE6IndexSquares i) : T1 :=
  T1_of_five_published_inputs_cfsg_and_remaining_after_twistedE6_outer
    lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow
    (fun i _ _ hn hi =>
      CFSGReduction.modelBoundsAfterFFourTwistedE6Squares_of_remaining_after_triality_outer
        i hi (fun h => remainingSimpleIndex i hn h))

theorem allTargets_of_five_published_inputs_cfsg_and_remaining_after_triality_outer
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
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterTrialityOuter i →
        CFSGReduction.ModelBoundsAfterFFourTwistedE6IndexSquares i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_five_published_inputs_cfsg_and_remaining_after_triality_outer
      lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
