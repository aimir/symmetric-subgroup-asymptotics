import SymmetricSubgroupAsymptotics.CFSGSevenTargetsMathieuTwentyThreeGoodSylow
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeActualIndexSquare

/-! M23 now retains only its outer numerical payload. Noncommutativity
is taken from the EXISTING numerical callback scope, not added as an
endpoint premise. All earlier reductions and published inputs remain. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def ModelBoundsAfterMathieuTwentyThreeIndexSquare : CFSG.Index → Prop
  | .sporadic .m23 => ∀ ell : ℕ, LeastProperIndex CFSG.Models.Presentations.M23.Model ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer CFSG.Models.Presentations.M23.Model))
  | i => ModelBoundsAfterMathieuTwelveIndexSquare i

theorem modelBoundsAfterMathieu12Square_of_after_Mathieu23_square
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model)
    (h : ModelBoundsAfterMathieuTwentyThreeIndexSquare i) :
    ModelBoundsAfterMathieuTwelveIndexSquare i := by
  cases i <;> try exact h
  case sporadic s hfinite hsimple =>
    cases s <;> try exact h
    case m23 =>
      letI : Finite CFSG.Models.Presentations.M23.Model := hfinite
      letI : IsSimpleGroup CFSG.Models.Presentations.M23.Model := hsimple
      intro ell hell
      exact ⟨CFSGMathieuTwentyThreeActualIndexSquare.index_square hn ell hell,h ell hell⟩

theorem simpleIndex_callback_after_Mathieu23_square
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterMathieuEleven i →
        ModelBoundsAfterMathieuTwentyThreeIndexSquare i)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingSufficientSimpleIndexAfterMathieuEleven i) :
    ModelBoundsAfterMathieuTwelveIndexSquare i :=
  modelBoundsAfterMathieu12Square_of_after_Mathieu23_square i hn (remaining i hn hi)

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu23_indexSquare
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuTwentyThree i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuEleven i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyThreeIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu23_goodSylow
    lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow
    (CFSGReduction.simpleIndex_callback_after_Mathieu23_square remainingSimpleIndex)

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_Mathieu23_indexSquare
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterMathieuTwentyThree i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuEleven i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyThreeIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_Mathieu23_indexSquare
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
