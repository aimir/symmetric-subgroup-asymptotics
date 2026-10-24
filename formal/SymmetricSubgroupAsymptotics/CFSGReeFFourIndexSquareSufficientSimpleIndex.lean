import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGReeGTwoIndexSquareSufficientSimpleIndex

/-! The original ReeF4 least-index square is proved. Its numerical
payload now retains only the outer-order budget. Other model payloads
are unchanged, including the separate Tits parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def ModelBoundsAfterReeFFourIndexSquare : CFSG.Index → Prop
  | .reeF4 m _ => ∀ ell : ℕ, LeastProperIndex (CFSG.Models.ReeF4 m) ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.ReeF4 m)))
  | i => ModelBoundsAfterReeGTwoIndexSquare i

theorem modelBoundsAfterReeGTwoSquare_of_after_ReeFFour_square
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (h : ModelBoundsAfterReeFFourIndexSquare i) : ModelBoundsAfterReeGTwoIndexSquare i := by
  cases i <;> try exact h
  case reeF4 m hm hfinite hsimple =>
    intro ell hell
    exact ⟨CFSGReeFFourOriginalIndexSquare.original_index_square m (by omega) ell hell,
      h ell hell⟩

end SymmetricSubgroupAsymptotics.CFSGReduction
