import SymmetricSubgroupAsymptotics.CFSGSevenTargetsMathieuTwentyThreeIndexSquare
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourGoodSylowTwentyThree

/-! The literal faithful24-point M24 representation supplies good Sylow23.
Only its good-Sylow callback tag is removed. The highest checked M23
index-square facade and all numerical scopes remain intact, including
M24's numerical payload and the four published bundles. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexAfterMathieuTwentyFour (i : CFSG.Index) : Prop :=
  RemainingGoodSylowIndexAfterMathieuTwentyThree i ∧ i ≠ .sporadic .m24

theorem goodSylow_callback_after_Mathieu24
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterMathieuTwentyFour i →
        ∃ p, GoodSylowPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterMathieuTwentyThree i) :
    ∃ p, GoodSylowPrime i.Model p := by
  by_cases hm : i = .sporadic .m24
  · subst i
    letI : Finite CFSG.Models.Presentations.M24.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .m24).Model))
    letI : IsSimpleGroup CFSG.Models.Presentations.M24.Model :=
      inferInstanceAs (IsSimpleGroup ((CFSG.Index.sporadic .m24).Model))
    exact ⟨23, CFSGMathieuTwentyFourGoodSylowTwentyThree.goodSylowPrime⟩
  · exact remaining i hn ⟨hi, hm⟩

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu24_goodSylow
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuTwentyFour i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuEleven i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyThreeIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu23_indexSquare
    lit hExceptionalOrbits hLMM hTracey hCFSG
    (CFSGReduction.goodSylow_callback_after_Mathieu24 remainingGoodSylow) remainingSimpleIndex

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_Mathieu24_goodSylow
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuTwentyFour i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuEleven i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyThreeIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu24_goodSylow
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
