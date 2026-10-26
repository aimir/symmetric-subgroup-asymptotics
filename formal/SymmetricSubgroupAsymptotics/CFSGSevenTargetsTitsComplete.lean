import SymmetricSubgroupAsymptotics.CFSGSevenTargetsTitsGoodSylow
import SymmetricSubgroupAsymptotics.CFSGTitsCompleteOuterBudget

/-! Both actual Tits model obligations are proved.  The optional endpoint
now retains only sporadic model callbacks, in addition to the unchanged
four published bundles and pinned CFSG. This is not CFSG-only T1. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingSufficientSimpleIndexAfterTits (i : CFSG.Index) : Prop :=
  RemainingSufficientSimpleIndexAfterReeFFourOuter i ∧ i≠.tits

theorem simpleIndex_callback_after_Tits
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterTits i →
        ModelBoundsAfterTitsIndexSquare i)
    (i : CFSG.Index) [Finite i.Model] [hsimple : IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model)
    (hi : RemainingSufficientSimpleIndexAfterReeFFourOuter i) :
    ModelBoundsAfterTitsIndexSquare i := by
  by_cases ht : i=.tits
  · subst i
    letI : IsSimpleGroup CFSG.Models.Tits := hsimple
    exact CFSGTitsCompleteOuterBudget.tits_sufficient_outer_budget
  · exact remaining i hn ⟨hi,ht⟩

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_Tits_complete
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterTits i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterTits i →
        CFSGReduction.ModelBoundsAfterTitsIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_Tits_goodSylow
    lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow
    (CFSGReduction.simpleIndex_callback_after_Tits remainingSimpleIndex)

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_Tits_complete
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterTits i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterTits i →
        CFSGReduction.ModelBoundsAfterTitsIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_Tits_complete
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
