import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGGTwoIndexSquareSufficientSimpleIndex

/-! The original ReeG2 index square is an actual theorem. Its remaining
simple-index payload therefore asks only for the outer-order budget. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def ModelBoundsAfterReeGTwoIndexSquare : CFSG.Index → Prop
  | .reeG2 m _ => ∀ell : ℕ,LeastProperIndex (CFSG.Models.ReeG2 m) ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.ReeG2 m)))
  | i => ModelBoundsAfterGTwoIndexSquare i

theorem modelBoundsAfterGTwoSquare_of_after_ReeGTwo_square
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (h : ModelBoundsAfterReeGTwoIndexSquare i) : ModelBoundsAfterGTwoIndexSquare i := by
  cases i <;> try exact h
  case reeG2 m hm hfinite hsimple =>
    intro ell hell
    exact ⟨CFSGReeGTwoOriginalIndexSquare.original_index_square m hm ell hell,h ell hell⟩

end SymmetricSubgroupAsymptotics.CFSGReduction
