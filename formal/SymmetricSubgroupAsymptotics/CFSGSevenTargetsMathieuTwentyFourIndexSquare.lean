import SymmetricSubgroupAsymptotics.CFSGSevenTargetsMathieuTwentyFourGoodSylow
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourActualIndexSquare

/-! M24's least-index square is supplied by the literal24-action and generic
successor-degree transfer theorem. The remaining numerical M24 payload is
outer-only. The21-sporadic good-Sylow guard, all other numerical scopes,
and four published bundles remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def ModelBoundsAfterMathieuTwentyFourIndexSquare : CFSG.Index → Prop
  | .sporadic .m24 => ∀ ell : ℕ, LeastProperIndex CFSG.Models.Presentations.M24.Model ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer CFSG.Models.Presentations.M24.Model))
  | i => ModelBoundsAfterMathieuTwentyThreeIndexSquare i

theorem modelBoundsAfterMathieu23Square_of_after_Mathieu24_square
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (h : ModelBoundsAfterMathieuTwentyFourIndexSquare i) :
    ModelBoundsAfterMathieuTwentyThreeIndexSquare i := by
  cases i <;> try exact h
  case sporadic s hfinite hsimple =>
    cases s <;> try exact h
    case m24 =>
      letI : Finite CFSG.Models.Presentations.M24.Model := hfinite
      letI : IsSimpleGroup CFSG.Models.Presentations.M24.Model := hsimple
      intro ell hell
      exact ⟨CFSGMathieuTwentyFourActualIndexSquare.index_square ell hell, h ell hell⟩

theorem simpleIndex_callback_after_Mathieu24_square
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterMathieuEleven i →
        ModelBoundsAfterMathieuTwentyFourIndexSquare i)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingSufficientSimpleIndexAfterMathieuEleven i) :
    ModelBoundsAfterMathieuTwentyThreeIndexSquare i :=
  modelBoundsAfterMathieu23Square_of_after_Mathieu24_square i (remaining i hn hi)

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu24_indexSquare
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuTwentyFour i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuEleven i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu24_goodSylow
    lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow
    (CFSGReduction.simpleIndex_callback_after_Mathieu24_square remainingSimpleIndex)

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_Mathieu24_indexSquare
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuTwentyFour i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuEleven i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu24_indexSquare
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
