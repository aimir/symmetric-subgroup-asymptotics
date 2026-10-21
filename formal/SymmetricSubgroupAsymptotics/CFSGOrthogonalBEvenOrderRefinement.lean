import SymmetricSubgroupAsymptotics.CFSGOrthogonalDEvenOrderRefinement
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBModelEvenOrder

/-! Removes the complete original type-B branch from the exact remaining
even-order obligations. Other unresolved families remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def OrthogonalBIndex : CFSG.Index→Prop
  | .B _ _ _=>True
  | _=>False

theorem orthogonalBIndex_even_card (i : CFSG.Index) [IsSimpleGroup i.Model]
    (hi : OrthogonalBIndex i) : Even (Nat.card i.Model) := by
  cases i <;> try contradiction
  case B r q hr hsimple=>
    letI : IsSimpleGroup (CFSG.Models.B r q) := hsimple
    exact CFSGOrthogonalBSerreMatrices.typeB_even_card r q (by omega)

def RemainingEvenOrderModelAfterOrthogonalB (i : CFSG.Index) : Prop :=
  RemainingEvenOrderModelAfterOrthogonalD i ∧ ¬OrthogonalBIndex i

theorem evenOrder_model_or_remaining_after_orthogonalB (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelAfterOrthogonalB i := by
  by_cases hB : OrthogonalBIndex i
  · exact Or.inl (orthogonalBIndex_even_card i hB)
  rcases evenOrder_model_or_remaining_after_orthogonalD i hn with h|h
  · exact Or.inl h
  · exact Or.inr ⟨h,hB⟩

theorem odd_order_solvable_of_cfsg_and_remaining_models_after_orthogonalB
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀(i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model→RemainingEvenOrderModelAfterOrthogonalB i→Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_after_orthogonalB i hn with h|h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
