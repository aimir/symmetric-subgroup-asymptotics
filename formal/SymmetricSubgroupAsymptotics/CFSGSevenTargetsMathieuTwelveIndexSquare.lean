import SymmetricSubgroupAsymptotics.CFSGSevenTargetsMathieuTwelveGoodSylow
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualIndexSquare

/-! The actual pinned M12 least-index square is supplied internally. Its
remaining numerical payload asks only for the sufficient outer budget.
All other numerical callback scopes, the23-sporadic good-Sylow guard, and
the four published bundles remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def ModelBoundsAfterMathieuTwelveIndexSquare : CFSG.Index → Prop
  | .sporadic .m12 => ∀ ell : ℕ, LeastProperIndex CFSG.Models.Presentations.M12.Model ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer CFSG.Models.Presentations.M12.Model))
  | i => ModelBoundsAfterMathieuTwentyTwoIndexSquare i

theorem modelBoundsAfterMathieu22Square_of_after_Mathieu12_square
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (h : ModelBoundsAfterMathieuTwelveIndexSquare i) :
    ModelBoundsAfterMathieuTwentyTwoIndexSquare i := by
  cases i <;> try exact h
  case sporadic s hfinite hsimple =>
    cases s <;> try exact h
    case m12 =>
      letI : Finite CFSG.Models.Presentations.M12.Model := hfinite
      letI : IsSimpleGroup CFSG.Models.Presentations.M12.Model := hsimple
      intro ell hell
      exact ⟨CFSGMathieuTwelveActualIndexSquare.index_square ell hell, h ell hell⟩

theorem simpleIndex_callback_after_Mathieu12_square
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterMathieuEleven i →
        ModelBoundsAfterMathieuTwelveIndexSquare i)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingSufficientSimpleIndexAfterMathieuEleven i) :
    ModelBoundsAfterMathieuTwentyTwoIndexSquare i :=
  modelBoundsAfterMathieu22Square_of_after_Mathieu12_square i (remaining i hn hi)

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu12_indexSquare
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuTwelve i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuEleven i →
        CFSGReduction.ModelBoundsAfterMathieuTwelveIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu12_goodSylow
    lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow
    (CFSGReduction.simpleIndex_callback_after_Mathieu12_square remainingSimpleIndex)

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_Mathieu12_indexSquare
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuTwelve i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuEleven i →
        CFSGReduction.ModelBoundsAfterMathieuTwelveIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu12_indexSquare
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
