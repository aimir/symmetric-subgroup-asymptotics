import SymmetricSubgroupAsymptotics.CFSGSevenTargetsTitsComplete
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoActualIndexSquare

/-! The actual M22 least-index square is supplied internally. Its SAME
remaining sporadic tag now asks only for the sufficient outer budget.
All good-Sylow obligations and four published bundles remain explicit;
this is not a CFSG-only T1 endpoint. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def ModelBoundsAfterMathieuTwentyTwoIndexSquare : CFSG.Index → Prop
  | .sporadic .m22 => ∀ ell : ℕ, LeastProperIndex CFSG.Models.Mathieu22 ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer CFSG.Models.Mathieu22))
  | i => ModelBoundsAfterTitsIndexSquare i

theorem modelBoundsAfterTitsSquare_of_after_Mathieu22_square
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (h : ModelBoundsAfterMathieuTwentyTwoIndexSquare i) :
    ModelBoundsAfterTitsIndexSquare i := by
  cases i <;> try exact h
  case sporadic s hfinite hsimple =>
    cases s <;> try exact h
    case m22 =>
      letI : Finite CFSG.Models.Mathieu22 := hfinite
      letI : IsSimpleGroup CFSG.Models.Mathieu22 := hsimple
      intro ell hell
      exact ⟨CFSGMathieuTwentyTwoActualIndexSquare.index_square ell hell,h ell hell⟩

theorem simpleIndex_callback_after_Mathieu22_square
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterTits i →
        ModelBoundsAfterMathieuTwentyTwoIndexSquare i)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingSufficientSimpleIndexAfterTits i) :
    ModelBoundsAfterTitsIndexSquare i :=
  modelBoundsAfterTitsSquare_of_after_Mathieu22_square i (remaining i hn hi)

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu22_indexSquare
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
        CFSGReduction.ModelBoundsAfterMathieuTwentyTwoIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_Tits_complete
    lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow
    (CFSGReduction.simpleIndex_callback_after_Mathieu22_square remainingSimpleIndex)

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_Mathieu22_indexSquare
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
        CFSGReduction.ModelBoundsAfterMathieuTwentyTwoIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu22_indexSquare
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
