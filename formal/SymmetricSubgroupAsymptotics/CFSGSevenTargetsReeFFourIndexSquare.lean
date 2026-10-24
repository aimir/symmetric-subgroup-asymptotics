import SymmetricSubgroupAsymptotics.CFSGSevenTargetsReeFFourGoodSylow
import SymmetricSubgroupAsymptotics.CFSGReeFFourIndexSquareSufficientSimpleIndex

/-! The final targets after the original ReeF4 least-index square.
Four published bundles and the explicit remaining model callbacks are
still parameters; this is not a CFSG-only endpoint. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_ReeFFour_indexSquare
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterReeFFour i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterReeGTwoOuter i →
          CFSGReduction.ModelBoundsAfterReeFFourIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_ReeFFour_goodSylow
    lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow
    (by
      intro i hfinite hsimple hn hi
      exact CFSGReduction.modelBoundsAfterReeGTwoSquare_of_after_ReeFFour_square
        i (remainingSimpleIndex i hn hi))

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_ReeFFour_indexSquare
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterReeFFour i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterReeGTwoOuter i →
          CFSGReduction.ModelBoundsAfterReeFFourIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_ReeFFour_indexSquare
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
