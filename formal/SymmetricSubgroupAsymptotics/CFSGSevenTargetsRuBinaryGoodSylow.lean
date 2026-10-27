import SymmetricSubgroupAsymptotics.CFSGSevenTargetsMathieuTwentyFourComplete
import SymmetricSubgroupAsymptotics.CFSGRuBinaryPowerGoodSylow

/-! Only the original Ru good-Sylow tag is discharged here, using actual
whole-matrix binary-power certificates and pinned CFSG. The numerical
guard/payload after M24, four published bundles, and all other remaining
good-Sylow obligations are retained. No power/capacity premise is added. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexAfterRuBinary (i : CFSG.Index) : Prop :=
  RemainingGoodSylowIndexAfterMathieuTwentyFour i ∧ i ≠ .sporadic .ru

theorem goodSylow_callback_after_Ru_binary
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterRuBinary i →
        ∃ p, GoodSylowPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterMathieuTwentyFour i) :
    ∃ p, GoodSylowPrime i.Model p := by
  by_cases hm : i = .sporadic .ru
  · subst i
    letI : Finite CFSG.Models.MatrixGroups.Ru.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .ru).Model))
    letI : IsSimpleGroup CFSG.Models.MatrixGroups.Ru.Model :=
      inferInstanceAs (IsSimpleGroup ((CFSG.Index.sporadic .ru).Model))
    exact ⟨2, CFSGRuBinaryPowerGoodSylow.goodSylowPrime hCFSG hn⟩
  · exact remaining i hn ⟨hi,hm⟩

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_Ru_binary
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterRuBinary i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwentyFourComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu24_complete
    lit hExceptionalOrbits hLMM hTracey hCFSG
    (CFSGReduction.goodSylow_callback_after_Ru_binary hCFSG remainingGoodSylow) remainingSimpleIndex

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_Ru_binary
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterRuBinary i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwentyFourComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_Ru_binary
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
