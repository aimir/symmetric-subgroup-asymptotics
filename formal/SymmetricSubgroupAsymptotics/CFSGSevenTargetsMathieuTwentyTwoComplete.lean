import SymmetricSubgroupAsymptotics.CFSGSevenTargetsMathieuTwelveComplete
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoOuterComplete

/-! Both M22 numerical obligations are now supplied internally. M22 is
absent from the remaining numerical guard, while all M24 refinements and
the21-sporadic good-Sylow guard are retained. Four published bundles and
pinned CFSG remain explicit; this is not a CFSG-only endpoint. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingSufficientSimpleIndexAfterMathieuTwentyTwoComplete (i : CFSG.Index) : Prop :=
  RemainingSufficientSimpleIndexAfterMathieuTwelveComplete i ∧ i ≠ .sporadic .m22

theorem simpleIndex_callback_after_Mathieu22_complete
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterMathieuTwentyTwoComplete i →
        ModelBoundsAfterMathieuTwentyFourIndexSquare i)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingSufficientSimpleIndexAfterMathieuTwelveComplete i) :
    ModelBoundsAfterMathieuTwentyFourIndexSquare i := by
  by_cases hm : i = .sporadic .m22
  · subst i
    letI : IsSimpleGroup CFSG.Models.Mathieu22 :=
      inferInstanceAs (IsSimpleGroup ((CFSG.Index.sporadic .m22).Model))
    exact CFSGMathieuTwentyTwoOuterComplete.sufficient_outer_budget
  · exact remaining i hn ⟨hi,hm⟩

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu22_complete
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuTwentyFour i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwentyTwoComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu12_complete
    lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow
    (CFSGReduction.simpleIndex_callback_after_Mathieu22_complete remainingSimpleIndex)

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_Mathieu22_complete
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuTwentyFour i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwentyTwoComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu22_complete
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
