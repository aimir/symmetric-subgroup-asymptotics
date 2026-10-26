import SymmetricSubgroupAsymptotics.CFSGSevenTargetsMathieuElevenGoodSylow
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenActualIndexSquare

/-! The actual pinned M11 least-index square is supplied internally. Its
remaining numerical tag asks only for the sufficient outer budget. The
24-sporadic good-Sylow guard and four published bundles remain explicit;
this is not a CFSG-only T1 endpoint. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def ModelBoundsAfterMathieuElevenIndexSquare : CFSG.Index → Prop
  | .sporadic .m11 => ∀ ell : ℕ, LeastProperIndex CFSG.Models.Presentations.M11.Model ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer CFSG.Models.Presentations.M11.Model))
  | i => ModelBoundsAfterMathieuTwentyTwoIndexSquare i

theorem modelBoundsAfterMathieu22Square_of_after_Mathieu11_square
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (h : ModelBoundsAfterMathieuElevenIndexSquare i) :
    ModelBoundsAfterMathieuTwentyTwoIndexSquare i := by
  cases i <;> try exact h
  case sporadic s hfinite hsimple =>
    cases s <;> try exact h
    case m11 =>
      letI : Finite CFSG.Models.Presentations.M11.Model := hfinite
      letI : IsSimpleGroup CFSG.Models.Presentations.M11.Model := hsimple
      intro ell hell
      exact ⟨CFSGMathieuElevenActualIndexSquare.index_square ell hell,h ell hell⟩

theorem simpleIndex_callback_after_Mathieu11_square
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterTits i →
        ModelBoundsAfterMathieuElevenIndexSquare i)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingSufficientSimpleIndexAfterTits i) :
    ModelBoundsAfterMathieuTwentyTwoIndexSquare i :=
  modelBoundsAfterMathieu22Square_of_after_Mathieu11_square i (remaining i hn hi)

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu11_indexSquare
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuEleven i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterTits i →
        CFSGReduction.ModelBoundsAfterMathieuElevenIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu11_goodSylow
    lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow
    (CFSGReduction.simpleIndex_callback_after_Mathieu11_square remainingSimpleIndex)

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_Mathieu11_indexSquare
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuEleven i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterTits i →
        CFSGReduction.ModelBoundsAfterMathieuElevenIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu11_indexSquare
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
