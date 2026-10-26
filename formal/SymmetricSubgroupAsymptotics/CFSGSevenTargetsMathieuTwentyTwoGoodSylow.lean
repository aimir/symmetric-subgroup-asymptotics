import SymmetricSubgroupAsymptotics.CFSGSevenTargetsMathieuTwentyTwoIndexSquare
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoGoodSylowEleven

/-! Actual M22 good-Sylow data remove exactly its tag from the separate
remaining good-Sylow callback. The26-sporadic numerical guard and its
outer-only M22 payload remain explicit, along with the four published
bundles and pinned CFSG. This is not CFSG-only T1. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexAfterMathieuTwentyTwo (i : CFSG.Index) : Prop :=
  RemainingGoodSylowIndexAfterTits i ∧ i≠.sporadic .m22

theorem goodSylow_callback_after_Mathieu22
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterMathieuTwentyTwo i →
        ∃ p, GoodSylowPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterTits i) :
    ∃ p, GoodSylowPrime i.Model p := by
  by_cases hm : i=.sporadic .m22
  · subst i
    exact ⟨11,CFSGMathieuTwentyTwoGoodSylowEleven.goodSylowPrime⟩
  · exact remaining i hn ⟨hi,hm⟩

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu22_goodSylow
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuTwentyTwo i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterTits i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyTwoIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu22_indexSquare
    lit hExceptionalOrbits hLMM hTracey hCFSG
    (CFSGReduction.goodSylow_callback_after_Mathieu22 remainingGoodSylow) remainingSimpleIndex

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_Mathieu22_goodSylow
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuTwentyTwo i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterTits i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyTwoIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu22_goodSylow
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
