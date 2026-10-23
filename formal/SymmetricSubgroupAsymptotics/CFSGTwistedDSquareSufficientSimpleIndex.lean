import SymmetricSubgroupAsymptotics.CFSGTwistedDIndexSquare
import SymmetricSubgroupAsymptotics.CFSGUnitarySquareSufficientSimpleIndex

/-! The proved original twisted-D index square removes its numerical
premise from the model callback. Both remaining twisted classical
branches request only the outer-order budget. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def ModelBoundsAfterTwistedDSquare : CFSG.Index → Prop
  | .twistedD r q _ => ∀ ell : ℕ, LeastProperIndex (CFSG.Models.TwistedD r q) ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.TwistedD r q)))
  | i => ModelBoundsAfterUnitarySquare i

theorem modelBoundsAfterUnitarySquare_of_after_twistedD_square
    (i : CFSG.Index) [IsSimpleGroup i.Model] (h : ModelBoundsAfterTwistedDSquare i) :
    ModelBoundsAfterUnitarySquare i := by
  cases i <;> try exact h
  case twistedD r q hr hsimple =>
    letI : IsSimpleGroup (CFSG.Models.TwistedD r q) := hsimple
    intro ell hell
    exact ⟨typeTwistedD_leastProperIndex_square_lt_card r q hr ell hell, h ell hell⟩

end SymmetricSubgroupAsymptotics.CFSGReduction
