import SymmetricSubgroupAsymptotics.CFSGSevenTargetsMathieuTwentyTwoGoodSylow
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenGoodSylowTwo

/-! The actual pinned M11 good-Sylow proof removes its tag from the
remaining good-Sylow callback. The26-sporadic numerical guard and all
other published and numerical payloads remain explicit. This is not a
CFSG-only T1 endpoint. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexAfterMathieuEleven (i : CFSG.Index) : Prop :=
  RemainingGoodSylowIndexAfterMathieuTwentyTwo i ∧ i≠.sporadic .m11

theorem goodSylow_callback_after_Mathieu11
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterMathieuEleven i →
        ∃ p, GoodSylowPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterMathieuTwentyTwo i) :
    ∃ p, GoodSylowPrime i.Model p := by
  by_cases hm : i=.sporadic .m11
  · subst i
    letI : Finite CFSG.Models.Presentations.M11.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .m11).Model))
    letI : IsSimpleGroup CFSG.Models.Presentations.M11.Model :=
      inferInstanceAs (IsSimpleGroup ((CFSG.Index.sporadic .m11).Model))
    exact ⟨2,CFSGMathieuElevenGoodSylowTwo.goodSylowPrime⟩
  · exact remaining i hn ⟨hi,hm⟩

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu11_goodSylow
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuEleven i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterTits i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyTwoIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu22_goodSylow
    lit hExceptionalOrbits hLMM hTracey hCFSG
    (CFSGReduction.goodSylow_callback_after_Mathieu11 remainingGoodSylow) remainingSimpleIndex

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_Mathieu11_goodSylow
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuEleven i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterTits i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyTwoIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu11_goodSylow
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
