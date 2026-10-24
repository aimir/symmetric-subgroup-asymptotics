import SymmetricSubgroupAsymptotics.CFSGSevenTargetsReeFFourIndexSquare
import SymmetricSubgroupAsymptotics.CFSGReeFFourCompleteSufficientSimpleIndex

/-! The original ReeF4 family no longer appears in either model
callback. Four published bundles and the remaining Tits/sporadic model
obligations remain explicit; this is not a CFSG-only T1 endpoint. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_ReeFFour_outer
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
        CFSGReduction.RemainingSufficientSimpleIndexAfterReeFFourOuter i →
          CFSGReduction.ModelBoundsAfterReeFFourIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_ReeFFour_indexSquare
    lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow
    (by
      intro i hfinite hsimple hn hi
      exact CFSGReduction.modelBoundsAfterReeFFourSquare_of_remaining_after_ReeFFour_outer
        i hi (remainingSimpleIndex i hn))

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_ReeFFour_outer
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
        CFSGReduction.RemainingSufficientSimpleIndexAfterReeFFourOuter i →
          CFSGReduction.ModelBoundsAfterReeFFourIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_ReeFFour_outer
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
