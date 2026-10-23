import SymmetricSubgroupAsymptotics.CFSGSevenTargetsGTwoOuter
import SymmetricSubgroupAsymptotics.CFSGGTwoCompleteSufficientSimpleIndex
import SymmetricSubgroupAsymptotics.CFSGReeGTwoGoodSylowReduction

/-! T1 additionally discharges the actual ReeG2 good-Sylow obligation.
Five published inputs, pinned CFSG and two explicit residual callbacks remain.
ReeG2 is retained in the independent simple-index/outer-order callback. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_five_published_inputs_cfsg_and_remaining_after_ReeGTwo_goodSylow
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
        CFSGReduction.ModelBoundsAfterGTwoIndexSquare i) : T1 := by
  apply T1_of_five_published_inputs_cfsg_and_remaining_after_GTwo_outer
    lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG _ remainingSimpleIndex
  intro i _ _ hn _
  rcases CFSGReduction.model_goodSylow_or_remaining_after_ReeGTwo i hn with h | h
  · exact h
  · exact remainingGoodSylow i hn h

theorem allTargets_of_five_published_inputs_cfsg_and_remaining_after_ReeGTwo_goodSylow
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
        CFSGReduction.ModelBoundsAfterGTwoIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_five_published_inputs_cfsg_and_remaining_after_ReeGTwo_goodSylow
      lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
