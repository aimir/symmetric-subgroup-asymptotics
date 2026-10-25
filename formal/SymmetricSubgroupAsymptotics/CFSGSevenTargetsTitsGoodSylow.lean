import SymmetricSubgroupAsymptotics.CFSGSevenTargetsTitsIndexSquare
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryConditionalGoodSylow
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterSaving

/-! Actual Tits good-Sylow data remove its tag from the remaining
good-Sylow callback. The four published bundles and the separate
simple-index/outer callback remain explicit. This is not CFSG-only T1. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem tits_goodSylowPrime : GoodSylowPrime CFSG.Models.Tits 2 :=
  CFSGReeFFourBinaryConditionalGoodSylow.tits_goodSylowPrime
    (CFSGReeFFourBinaryOuterSaving.outer_mem_derived 0)

def RemainingGoodSylowIndexAfterTits (i : CFSG.Index) : Prop :=
  RemainingGoodSylowIndexAfterReeFFour i ∧ i ≠ .tits

theorem goodSylow_callback_after_Tits
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterTits i →
        ∃ p, GoodSylowPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterReeFFour i) :
    ∃ p, GoodSylowPrime i.Model p := by
  by_cases ht : i = .tits
  · subst i
    exact ⟨2, tits_goodSylowPrime⟩
  · exact remaining i hn ⟨hi, ht⟩

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_Tits_goodSylow
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterTits i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterReeFFourOuter i →
          CFSGReduction.ModelBoundsAfterTitsIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_Tits_indexSquare
    lit hExceptionalOrbits hLMM hTracey hCFSG
    (CFSGReduction.goodSylow_callback_after_Tits remainingGoodSylow) remainingSimpleIndex

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_Tits_goodSylow
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterTits i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterReeFFourOuter i →
          CFSGReduction.ModelBoundsAfterTitsIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_Tits_goodSylow
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
