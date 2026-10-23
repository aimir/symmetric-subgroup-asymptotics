import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGUnitaryCompleteSufficientSimpleIndex

/-! The original triality index square is proved. Its remaining model
data ask only for the outer budget; all other surviving obligations and
the discharged unitary/nonsplit-D cases are preserved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def ModelBoundsAfterTrialityIndexSquare : CFSG.Index → Prop
  | .trialityD4 q => ∀ ell : ℕ, LeastProperIndex (CFSG.Models.TrialityD4 q) ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.TrialityD4 q)))
  | i => ModelBoundsAfterTwistedDSquare i

theorem modelBoundsAfterTwistedDSquare_of_after_triality_index_square
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (h : ModelBoundsAfterTrialityIndexSquare i) : ModelBoundsAfterTwistedDSquare i := by
  cases i <;> try exact h
  case trialityD4 q hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := hsimple
    intro ell hell
    exact ⟨CFSGTrialityGeckOriginalIndexSquare.original_index_square q ell hell,h ell hell⟩

end SymmetricSubgroupAsymptotics.CFSGReduction
