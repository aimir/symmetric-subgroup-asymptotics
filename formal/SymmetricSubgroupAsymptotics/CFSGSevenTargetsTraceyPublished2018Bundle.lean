import SymmetricSubgroupAsymptotics.CFSGSevenTargetsReeGTwoOuter
import SymmetricSubgroupAsymptotics.TraceyPublished2018PermutationBundle

/-! Optional dependency consolidation using both explicitly retained
published conclusions of Tracey 2018. This stronger published bundle
supplies the old coarse Tracey input AND the independent MN consequence.
The original inputs and endpoints are unchanged. Four published inputs,
pinned CFSG and both stated residual model callbacks still remain;
neither the Tracey bundle nor either callback is proved from CFSG here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_with_tracey2018_bundle
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterReeGTwo i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterReeGTwoOuter i →
          CFSGReduction.ModelBoundsAfterReeGTwoIndexSquare i) : T1 := by
  exact T1_of_five_published_inputs_cfsg_and_remaining_after_ReeGTwo_outer
    lit hExceptionalOrbits hLMM hTracey.coarse hTracey.mcIverNeumann hCFSG
    remainingGoodSylow remainingSimpleIndex

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_with_tracey2018_bundle
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterReeGTwo i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterReeGTwoOuter i →
          CFSGReduction.ModelBoundsAfterReeGTwoIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_with_tracey2018_bundle
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
