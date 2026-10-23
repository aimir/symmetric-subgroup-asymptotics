import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGFFourCompleteSufficientSimpleIndex

/-! G2's original index square is discharged from the remaining model
data. Its outer-order budget is still explicit; every other branch is
unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def ModelBoundsAfterGTwoIndexSquare : CFSG.Index → Prop
  | .G2 q _ => ∀ ell : ℕ, LeastProperIndex (CFSG.Models.G2 q) ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.G2 q)))
  | i => ModelBoundsAfterFFourTwistedE6IndexSquares i

theorem modelBoundsAfterFFourTwistedE6Squares_of_after_GTwo_square
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (h : ModelBoundsAfterGTwoIndexSquare i) :
    ModelBoundsAfterFFourTwistedE6IndexSquares i := by
  cases i <;> try exact h
  case G2 q hsmall hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.G2 q) := hsimple
    intro ell hell
    exact ⟨CFSGGTwoOriginalIndexSquare.typeGTwo_index_square q hsmall ell hell,h ell hell⟩

end SymmetricSubgroupAsymptotics.CFSGReduction
