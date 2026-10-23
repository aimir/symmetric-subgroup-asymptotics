import SymmetricSubgroupAsymptotics.CFSGUnitaryAdmissibleIndexSquare
import SymmetricSubgroupAsymptotics.CFSGExceptionalSufficientSimpleIndexReduction

/-! After the proved unitary index squares, that residual branch asks
only for its outer-order budget. Other remaining model bounds stay
explicit and unchanged. This is not a completed CFSG reduction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure CFSGTwistedAUnitaryCoordinates

def ModelBoundsAfterUnitarySquare : CFSG.Index → Prop
  | .twistedA r q _ _ => ∀ ell : ℕ, LeastProperIndex (CFSG.Models.TwistedA r q) ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.TwistedA r q)))
  | i => ModelSufficientSimpleIndexBounds i

theorem modelSufficientSimpleIndexBounds_of_after_unitary_square (i : CFSG.Index)
    (h : ModelBoundsAfterUnitarySquare i) : ModelSufficientSimpleIndexBounds i := by
  cases i <;> try exact h
  case twistedA r q hr hsmall =>
    intro ell hell
    exact ⟨twistedA_admissible_leastIndex_square_lt r hr q hsmall ell hell, h ell hell⟩

theorem sufficientSimpleIndexBounds_of_cfsg_after_unitary_square
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterExceptionalE i →
        ModelBoundsAfterUnitarySquare i) : SufficientSimpleIndexBounds := by
  apply sufficientSimpleIndexBounds_of_cfsg_and_remaining_after_exceptional_E hCFSG
  intro i _ _ hn hi
  exact modelSufficientSimpleIndexBounds_of_after_unitary_square i (remaining i hn hi)

end SymmetricSubgroupAsymptotics.CFSGReduction
