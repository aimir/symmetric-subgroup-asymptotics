import SymmetricSubgroupAsymptotics.CFSGClassicalSufficientSimpleIndexReduction
import SymmetricSubgroupAsymptotics.CFSGExceptionalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGExceptionalOuterBudget

/-! All untwisted exceptional E models leave the sufficient simple-index
residual. Their original index squares and actual outer budgets are proved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure CFSGExceptionalIndexSquare CFSGExceptionalOuterBudget

def RemainingSufficientSimpleIndexAfterExceptionalE : CFSG.Index → Prop
  | .E6 _ => False
  | .E7 _ => False
  | .E8 _ => False
  | i => RemainingSufficientSimpleIndexModelWithoutClassicalSuzuki i

theorem sufficientSimpleIndex_model_or_remaining_after_exceptional_E (i : CFSG.Index)
    [Finite i.Model] [IsSimpleGroup i.Model] (hn : ¬ IsMulCommutative i.Model) :
    ModelSufficientSimpleIndexBounds i ∨ RemainingSufficientSimpleIndexAfterExceptionalE i := by
  cases i <;> try exact sufficientSimpleIndex_model_or_remaining_without_classical_suzuki _ hn
  case E6 q hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.E6 q) := hsimple
    letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
    left
    intro ell hell
    exact ⟨typeE6_leastIndex_square_lt q ell hell,
      serreTypeE6_sufficient_outer_budget q.Field q.prime ell hell⟩
  case E7 q hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.E7 q) := hsimple
    letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
    left
    intro ell hell
    exact ⟨typeE7_leastIndex_square_lt q ell hell,
      serreTypeE7_sufficient_outer_budget q.Field q.prime ell hell⟩
  case E8 q hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.E8 q) := hsimple
    letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
    left
    intro ell hell
    exact ⟨typeE8_leastIndex_square_lt q ell hell,
      serreTypeE8_sufficient_outer_budget q.Field q.prime ell hell⟩

theorem sufficientSimpleIndexBounds_of_cfsg_and_remaining_after_exceptional_E
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterExceptionalE i →
        ModelSufficientSimpleIndexBounds i) : SufficientSimpleIndexBounds := by
  apply sufficientSimpleIndexBounds_of_cfsg_and_remaining_nonclassical_models hCFSG
  intro i _ _ hn _
  rcases sufficientSimpleIndex_model_or_remaining_after_exceptional_E i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
