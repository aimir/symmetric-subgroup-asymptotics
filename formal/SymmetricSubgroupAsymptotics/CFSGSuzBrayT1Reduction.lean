import SymmetricSubgroupAsymptotics.CFSGSporadicBinaryFramesT1Reduction
import SymmetricSubgroupAsymptotics.CFSGSuzOddRotationGoodSylow

/-! Successor removing ONLY Suz from the remaining Good-Sylow callback.
The actual positive whole-matrix identities are imported by its native
consumer, not supplied to this endpoint. Three published bundles and the
independent numerical simple-index callback remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexAfterSuzBray (i : CFSG.Index) : Prop :=
  RemainingGoodSylowIndexAfterBinaryFrames i ∧ i ≠ .sporadic .suz

theorem goodSylow_callback_after_suz_bray
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterSuzBray i →
        ∃ p,GoodSylowPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterBinaryFrames i) :
    ∃ p,GoodSylowPrime i.Model p := by
  by_cases hs : i = .sporadic .suz
  · subst i
    letI : Finite CFSG.Models.MatrixGroups.Suz.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .suz).Model))
    exact ⟨2,CFSGSuzOddRotationGoodSylow.goodSylowPrime hCFSG hn⟩
  · exact remaining i hn ⟨hi,hs⟩

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

theorem T1_of_three_published_inputs_cfsg_and_remaining_after_suz_bray
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterSuzBray i →
        ∃ p,CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwentyFourComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : T1 :=
  T1_of_three_published_inputs_cfsg_and_remaining_after_binary_frames
    lit hExceptionalOrbits hTracey hCFSG
    (CFSGReduction.goodSylow_callback_after_suz_bray hCFSG remainingGoodSylow)
    remainingSimpleIndex

theorem allTargets_of_three_published_inputs_cfsg_and_remaining_after_suz_bray
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterSuzBray i →
        ∃ p,CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwentyFourComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_three_published_inputs_cfsg_and_remaining_after_suz_bray
      lit hExceptionalOrbits hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
