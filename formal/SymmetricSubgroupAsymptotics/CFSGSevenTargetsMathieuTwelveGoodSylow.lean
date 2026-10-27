import SymmetricSubgroupAsymptotics.CFSGSevenTargetsMathieuElevenComplete
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveGoodSylowEleven

/-! The actual pinned M12 good-Sylow proof supplies its good-Sylow tag.
The numerical M12 payload and the four published bundles remain explicit.
This endpoint retains the checked complete M11 reduction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexAfterMathieuTwelve (i : CFSG.Index) : Prop :=
  RemainingGoodSylowIndexAfterMathieuEleven i ∧ i ≠ .sporadic .m12

theorem goodSylow_callback_after_Mathieu12
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterMathieuTwelve i →
        ∃ p, GoodSylowPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterMathieuEleven i) :
    ∃ p, GoodSylowPrime i.Model p := by
  by_cases hm : i = .sporadic .m12
  · subst i
    letI : Finite CFSG.Models.Presentations.M12.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .m12).Model))
    letI : IsSimpleGroup CFSG.Models.Presentations.M12.Model :=
      inferInstanceAs (IsSimpleGroup ((CFSG.Index.sporadic .m12).Model))
    exact ⟨11, CFSGMathieuTwelveGoodSylowEleven.goodSylowPrime⟩
  · exact remaining i hn ⟨hi, hm⟩

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu12_goodSylow
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuTwelve i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuEleven i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyTwoIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu11_complete
    lit hExceptionalOrbits hLMM hTracey hCFSG
    (CFSGReduction.goodSylow_callback_after_Mathieu12 remainingGoodSylow) remainingSimpleIndex

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_Mathieu12_goodSylow
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuTwelve i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuEleven i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyTwoIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu12_goodSylow
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
