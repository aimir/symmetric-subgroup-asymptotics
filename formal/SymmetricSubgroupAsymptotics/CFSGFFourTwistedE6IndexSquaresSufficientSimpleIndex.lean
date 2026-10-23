import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGTrialityIndexSquareSufficientSimpleIndex

/-! The original F4 and twisted E6 index squares are proved. Their
remaining model-budget leaves now request only the outer-order bound.
The separate triality outer leaf and all other residuals are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def ModelBoundsAfterFFourTwistedE6IndexSquares : CFSG.Index → Prop
  | .F4 q => ∀ ell : ℕ, LeastProperIndex (CFSG.Models.F4 q) ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.F4 q)))
  | .twistedE6 q => ∀ ell : ℕ, LeastProperIndex (CFSG.Models.TwistedE6 q) ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.TwistedE6 q)))
  | i => ModelBoundsAfterTrialityIndexSquare i

theorem modelBoundsAfterTrialitySquare_of_after_fFour_twistedE6_squares
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (h : ModelBoundsAfterFFourTwistedE6IndexSquares i) : ModelBoundsAfterTrialityIndexSquare i := by
  cases i <;> try exact h
  case F4 q hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.F4 q) := hsimple
    letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
    intro ell hell
    exact ⟨CFSGFFourE6OriginalIndexSquare.original_index_square q.Field q.prime ell hell,
      h ell hell⟩
  case twistedE6 q hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := hsimple
    intro ell hell
    exact ⟨CFSGTwistedE6GeckOriginalIndexSquare.original_index_square q ell hell, h ell hell⟩

end SymmetricSubgroupAsymptotics.CFSGReduction
