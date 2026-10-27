import SymmetricSubgroupAsymptotics.CFSGTransitiveCountT1Reduction
import SymmetricSubgroupAsymptotics.CFSGJankoOneBinaryFrameGoodSylow
import SymmetricSubgroupAsymptotics.CFSGYBinaryDerivedFrames

/-! Two concrete binary frames generate the original J1 presentation and
all four pinned Y-derived simple sections. This removes precisely these
five tags from the good-Sylow callback. The three published bundles and
the independent numerical simple-index callback remain explicit inputs.
This is not a CFSG-only proof of T1. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexAfterBinaryFrames (i : CFSG.Index) : Prop :=
  RemainingGoodSylowIndexAfterONBinary i ∧ i ≠ .sporadic .j1 ∧
    i ≠ .sporadic .fi22 ∧ i ≠ .sporadic .fi23 ∧
    i ≠ .sporadic .fi24Prime ∧ i ≠ .sporadic .babyMonster

theorem goodSylow_callback_after_binary_frames
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterBinaryFrames i →
        ∃ p, GoodSylowPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterONBinary i) :
    ∃ p, GoodSylowPrime i.Model p := by
  by_cases hm : i = .sporadic .j1
  · subst i
    letI : Finite CFSG.Models.Presentations.J1.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .j1).Model))
    letI : IsSimpleGroup CFSG.Models.Presentations.J1.Model :=
      inferInstanceAs (IsSimpleGroup ((CFSG.Index.sporadic .j1).Model))
    exact ⟨2, CFSGJankoOneBinaryFrameGoodSylow.goodSylowPrime hCFSG⟩
  · by_cases hf22 : i = .sporadic .fi22
    · subst i
      letI : Finite (CFSG.Models.YGroups.SimpleSection CFSG.Models.YGroups.arms332) :=
        inferInstanceAs (Finite ((CFSG.Index.sporadic .fi22).Model))
      exact ⟨2, CFSGYBinaryDerivedFrames.goodSylowPrime CFSG.Models.YGroups.arms332 hCFSG⟩
    · by_cases hf23 : i = .sporadic .fi23
      · subst i
        letI : Finite (CFSG.Models.YGroups.SimpleSection CFSG.Models.YGroups.arms432) :=
          inferInstanceAs (Finite ((CFSG.Index.sporadic .fi23).Model))
        exact ⟨2, CFSGYBinaryDerivedFrames.goodSylowPrime CFSG.Models.YGroups.arms432 hCFSG⟩
      · by_cases hf24 : i = .sporadic .fi24Prime
        · subst i
          letI : Finite (CFSG.Models.YGroups.SimpleSection CFSG.Models.YGroups.arms442) :=
            inferInstanceAs (Finite ((CFSG.Index.sporadic .fi24Prime).Model))
          exact ⟨2, CFSGYBinaryDerivedFrames.goodSylowPrime CFSG.Models.YGroups.arms442 hCFSG⟩
        · by_cases hb : i = .sporadic .babyMonster
          · subst i
            letI : Finite (CFSG.Models.YGroups.SimpleSection CFSG.Models.YGroups.arms433) :=
              inferInstanceAs (Finite ((CFSG.Index.sporadic .babyMonster).Model))
            exact ⟨2, CFSGYBinaryDerivedFrames.goodSylowPrime CFSG.Models.YGroups.arms433 hCFSG⟩
          · exact remaining i hn ⟨hi, hm, hf22, hf23, hf24, hb⟩

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

theorem T1_of_three_published_inputs_cfsg_and_remaining_after_binary_frames
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterBinaryFrames i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwentyFourComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : T1 :=
  T1_of_three_published_inputs_cfsg_and_remaining_after_ON_binary
    lit hExceptionalOrbits hTracey hCFSG
    (CFSGReduction.goodSylow_callback_after_binary_frames hCFSG remainingGoodSylow)
    remainingSimpleIndex

theorem allTargets_of_three_published_inputs_cfsg_and_remaining_after_binary_frames
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterBinaryFrames i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwentyFourComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_three_published_inputs_cfsg_and_remaining_after_binary_frames
      lit hExceptionalOrbits hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
