import SymmetricSubgroupAsymptotics.CFSGSevenTargetsFFourOuter
import SymmetricSubgroupAsymptotics.CFSGGTwoIndexSquareSufficientSimpleIndex

/-! T1 with the original G2 index square proved. Five published inputs,
CFSG and two explicit residual model callbacks remain; the G2 payload
now asks only for the outer-order budget. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_five_published_inputs_cfsg_and_remaining_after_GTwo_index_square
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
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterFFourOuter i →
        CFSGReduction.ModelBoundsAfterGTwoIndexSquare i) : T1 :=
  T1_of_five_published_inputs_cfsg_and_remaining_after_fFour_outer
    lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow
    (fun i _ _ hn hi =>
      CFSGReduction.modelBoundsAfterFFourTwistedE6Squares_of_after_GTwo_square
        i (remainingSimpleIndex i hn hi))

theorem allTargets_of_five_published_inputs_cfsg_and_remaining_after_GTwo_index_square
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
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterFFourOuter i →
        CFSGReduction.ModelBoundsAfterGTwoIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_five_published_inputs_cfsg_and_remaining_after_GTwo_index_square
      lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
