import SymmetricSubgroupAsymptotics.CFSGSevenTargetsReeGTwoGoodSylow
import SymmetricSubgroupAsymptotics.CFSGReeGTwoIndexSquareSufficientSimpleIndex
import SymmetricSubgroupAsymptotics.CFSGGTwoCompleteSufficientSimpleIndex
import SymmetricSubgroupAsymptotics.CFSGReeGTwoGoodSylowReduction

/-! T1 discharges the actual ReeG2 good-Sylow and index-square obligations.
Five published inputs, pinned CFSG and two explicit residual callbacks remain.
The surviving ReeG2 payload asks only for its outer-order budget. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_five_published_inputs_cfsg_and_remaining_after_ReeGTwo_index_square
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterReeGTwo i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterGTwoOuter i →
        CFSGReduction.ModelBoundsAfterReeGTwoIndexSquare i) : T1 := by
  apply T1_of_five_published_inputs_cfsg_and_remaining_after_ReeGTwo_goodSylow
    lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow
  intro i _ _ hn hi
  exact CFSGReduction.modelBoundsAfterGTwoSquare_of_after_ReeGTwo_square i
    (remainingSimpleIndex i hn hi)

theorem allTargets_of_five_published_inputs_cfsg_and_remaining_after_ReeGTwo_index_square
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterReeGTwo i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterGTwoOuter i →
        CFSGReduction.ModelBoundsAfterReeGTwoIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_five_published_inputs_cfsg_and_remaining_after_ReeGTwo_index_square
      lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
