import SymmetricSubgroupAsymptotics.CFSGSevenTargetsMathieuTwentyFourIndexSquare
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveOuterBound

/-! M12's numerical payload is supplied by the complete checked original
fixed-generator count. Its tag is removed from the remaining numerical
callback. All M24 refinements and the21-sporadic good-Sylow guard remain;
four published bundles and pinned CFSG are still explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingSufficientSimpleIndexAfterMathieuTwelveComplete (i : CFSG.Index) : Prop :=
  RemainingSufficientSimpleIndexAfterMathieuEleven i ∧ i ≠ .sporadic .m12

theorem simpleIndex_callback_after_Mathieu12_complete
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterMathieuTwelveComplete i →
        ModelBoundsAfterMathieuTwentyFourIndexSquare i)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model)
    (hi : RemainingSufficientSimpleIndexAfterMathieuEleven i) :
    ModelBoundsAfterMathieuTwentyFourIndexSquare i := by
  by_cases hm : i = .sporadic .m12
  · subst i
    letI : Finite CFSG.Models.Presentations.M12.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .m12).Model))
    letI : IsSimpleGroup CFSG.Models.Presentations.M12.Model :=
      inferInstanceAs (IsSimpleGroup ((CFSG.Index.sporadic .m12).Model))
    exact CFSGMathieuTwelveOuterBound.sufficient_outer_budget
  · exact remaining i hn ⟨hi,hm⟩

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu12_complete
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuTwentyFour i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwelveComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu24_indexSquare
    lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow
    (CFSGReduction.simpleIndex_callback_after_Mathieu12_complete remainingSimpleIndex)

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_Mathieu12_complete
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuTwentyFour i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwelveComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu12_complete
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
