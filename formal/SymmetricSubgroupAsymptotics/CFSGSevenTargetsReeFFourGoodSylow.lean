import SymmetricSubgroupAsymptotics.CFSGSevenTargetsTraceyPublished2018Bundle
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalGoodSylow

/-! The original ReeF4 family is removed from the good-Sylow callback.
The simple-index callback and the four published inputs are unchanged;
this is not a CFSG-only T1 theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexAfterReeFFour (i : CFSG.Index) : Prop :=
  RemainingGoodSylowIndexAfterReeGTwo i ∧
    ∀ (m : ℕ) (hm : 1 ≤ m), i ≠ .reeF4 m hm

theorem goodSylow_callback_after_ReeFFour
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterReeFFour i →
        ∃ p, GoodSylowPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterReeGTwo i) :
    ∃ p, GoodSylowPrime i.Model p := by
  by_cases hree : ∃ (m : ℕ) (hm : 1 ≤ m), i = .reeF4 m hm
  · obtain ⟨m,hm,rfl⟩ := hree
    exact ⟨2,CFSGReeFFourOriginalGoodSylow.original_goodSylowPrime m (by omega)⟩
  · apply remaining i hn
    exact ⟨hi,fun m hm he => hree ⟨m,hm,he⟩⟩

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_ReeFFour_goodSylow
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterReeFFour i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterReeGTwoOuter i →
          CFSGReduction.ModelBoundsAfterReeGTwoIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_with_tracey2018_bundle
    lit hExceptionalOrbits hLMM hTracey hCFSG
    (CFSGReduction.goodSylow_callback_after_ReeFFour remainingGoodSylow) remainingSimpleIndex

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_ReeFFour_goodSylow
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterReeFFour i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterReeGTwoOuter i →
          CFSGReduction.ModelBoundsAfterReeGTwoIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_ReeFFour_goodSylow
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
