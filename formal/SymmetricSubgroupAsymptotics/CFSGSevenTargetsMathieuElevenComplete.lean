import SymmetricSubgroupAsymptotics.CFSGSevenTargetsMathieuElevenIndexSquare
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenOuterBound

/-! Both actual pinned M11 numerical obligations are supplied internally.
The numerical guard now excludes M11; its M22 payload still asks only for
the sufficient outer budget. The good-Sylow guard remains the checked
24-sporadic guard. Four published bundles and pinned CFSG are unchanged;
this is not a CFSG-only endpoint. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingSufficientSimpleIndexAfterMathieuEleven (i : CFSG.Index) : Prop :=
  RemainingSufficientSimpleIndexAfterTits i ∧ i ≠ .sporadic .m11

theorem simpleIndex_callback_after_Mathieu11_complete
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterMathieuEleven i →
        ModelBoundsAfterMathieuTwentyTwoIndexSquare i)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingSufficientSimpleIndexAfterTits i) :
    ModelBoundsAfterMathieuElevenIndexSquare i := by
  by_cases hm : i = .sporadic .m11
  · subst i
    letI : Finite CFSG.Models.Presentations.M11.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .m11).Model))
    letI : IsSimpleGroup CFSG.Models.Presentations.M11.Model :=
      inferInstanceAs (IsSimpleGroup ((CFSG.Index.sporadic .m11).Model))
    exact CFSGMathieuElevenOuterBound.sufficient_outer_budget
  · have h := remaining i hn ⟨hi,hm⟩
    cases i <;> try exact h
    next s hfinite hsimple =>
      cases s <;> try exact h
      next => exact (hm rfl).elim

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu11_complete
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuEleven i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuEleven i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyTwoIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu11_indexSquare
    lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow
    (CFSGReduction.simpleIndex_callback_after_Mathieu11_complete remainingSimpleIndex)

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_Mathieu11_complete
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuEleven i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuEleven i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyTwoIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu11_complete
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
