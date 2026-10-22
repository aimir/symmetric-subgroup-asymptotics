import SymmetricSubgroupAsymptotics.CFSGClassicalSufficientSimpleIndexReduction
import SymmetricSubgroupAsymptotics.CFSGExceptionalIndexSquare

/-! Only the outer-order budget remains for untwisted exceptional E.
The genuine original-model index-square theorem discharges that half
of the former sufficient simple-index callback. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def SufficientSimpleIndexRemainderAfterExceptionalSquares : CFSG.Index → Prop
  | .E6 q => ∀ ell : ℕ, LeastProperIndex (CFSG.Models.E6 q) ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.E6 q)))
  | .E7 q => ∀ ell : ℕ, LeastProperIndex (CFSG.Models.E7 q) ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.E7 q)))
  | .E8 q => ∀ ell : ℕ, LeastProperIndex (CFSG.Models.E8 q) ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.E8 q)))
  | i => ModelSufficientSimpleIndexBounds i

theorem modelSufficientSimpleIndexBounds_of_remainder_after_exceptional_squares
    (i : CFSG.Index) [IsSimpleGroup i.Model]
    (h : SufficientSimpleIndexRemainderAfterExceptionalSquares i) :
    ModelSufficientSimpleIndexBounds i := by
  cases i <;> try exact h
  case E6 q hsimple =>
    letI : IsSimpleGroup (CFSG.Models.E6 q) := hsimple
    intro ell hell
    exact ⟨CFSGExceptionalIndexSquare.typeE6_leastIndex_square_lt q ell hell, h ell hell⟩
  case E7 q hsimple =>
    letI : IsSimpleGroup (CFSG.Models.E7 q) := hsimple
    intro ell hell
    exact ⟨CFSGExceptionalIndexSquare.typeE7_leastIndex_square_lt q ell hell, h ell hell⟩
  case E8 q hsimple =>
    letI : IsSimpleGroup (CFSG.Models.E8 q) := hsimple
    intro ell hell
    exact ⟨CFSGExceptionalIndexSquare.typeE8_leastIndex_square_lt q ell hell, h ell hell⟩

end SymmetricSubgroupAsymptotics.CFSGReduction
