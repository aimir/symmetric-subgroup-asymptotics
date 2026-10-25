import SymmetricSubgroupAsymptotics.CFSGSevenTargetsReeFFourOuter
import SymmetricSubgroupAsymptotics.CFSGTitsOriginalIndexSquare

/-! The actual Tits least-index square is proved. Its remaining numerical
payload asks only for the outer-order budget; all other explicit inputs
are retained. This does not prove CFSG-only T1. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def ModelBoundsAfterTitsIndexSquare : CFSG.Index → Prop
  | .tits => ∀ ell : ℕ, LeastProperIndex CFSG.Models.Tits ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer CFSG.Models.Tits))
  | i => ModelBoundsAfterReeFFourIndexSquare i

theorem modelBoundsAfterReeFFourSquare_of_after_Tits_square
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (h : ModelBoundsAfterTitsIndexSquare i) :
    ModelBoundsAfterReeFFourIndexSquare i := by
  cases i <;> try exact h
  case tits hfinite hsimple =>
    letI : Finite CFSG.Models.Tits := hfinite
    letI : IsSimpleGroup CFSG.Models.Tits := hsimple
    intro ell hell
    exact ⟨CFSGTitsOriginalIndexSquare.index_square hn ell hell, h ell hell⟩

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_four_published_inputs_cfsg_and_remaining_after_Tits_indexSquare
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
        CFSGReduction.RemainingSufficientSimpleIndexAfterReeFFourOuter i →
          CFSGReduction.ModelBoundsAfterTitsIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_ReeFFour_outer
    lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow
    (by
      intro i hfinite hsimple hn hi
      letI := hfinite
      letI := hsimple
      exact CFSGReduction.modelBoundsAfterReeFFourSquare_of_after_Tits_square
        i hn (remainingSimpleIndex i hn hi))

theorem allTargets_of_four_published_inputs_cfsg_and_remaining_after_Tits_indexSquare
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
        CFSGReduction.RemainingSufficientSimpleIndexAfterReeFFourOuter i →
          CFSGReduction.ModelBoundsAfterTitsIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_four_published_inputs_cfsg_and_remaining_after_Tits_indexSquare
      lit hExceptionalOrbits hLMM hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
