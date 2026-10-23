import SymmetricSubgroupAsymptotics.CFSGSevenTargetsReeGTwoIndexSquare
import SymmetricSubgroupAsymptotics.CFSGReeGTwoCompleteSufficientSimpleIndex

/-! The pinned original ReeG2 branch is absent from both residual
callbacks. Five published inputs, pinned CFSG, and the explicitly
remaining model obligations are still required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_five_published_inputs_cfsg_and_remaining_after_ReeGTwo_outer
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
      ¬ IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterReeGTwoOuter i →
          CFSGReduction.ModelBoundsAfterReeGTwoIndexSquare i) : T1 := by
  apply T1_of_five_published_inputs_cfsg_and_remaining_after_ReeGTwo_index_square
    lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow
  intro i _ _ hn hi
  exact CFSGReduction.modelBoundsAfterReeGTwoSquare_of_remaining_after_ReeGTwo_outer
    i hi (remainingSimpleIndex i hn)

theorem allTargets_of_five_published_inputs_cfsg_and_remaining_after_ReeGTwo_outer
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
      ¬ IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterReeGTwoOuter i →
          CFSGReduction.ModelBoundsAfterReeGTwoIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_five_published_inputs_cfsg_and_remaining_after_ReeGTwo_outer
      lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
