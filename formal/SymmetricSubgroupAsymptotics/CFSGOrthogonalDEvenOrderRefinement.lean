import SymmetricSubgroupAsymptotics.CFSGSymplecticEvenOrderRefinement
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDModelEvenOrder

/-! The complete original type-D branch is removed from the exact
remaining even-order obligations, in all characteristics. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def OrthogonalDIndex : CFSG.Index → Prop
  | .D _ _ _ => True
  | _ => False

theorem orthogonalDIndex_even_card (i : CFSG.Index) [IsSimpleGroup i.Model]
    (hi : OrthogonalDIndex i) : Even (Nat.card i.Model) := by
  cases i <;> try contradiction
  case D r q hr hsimple =>
    letI : IsSimpleGroup (CFSG.Models.D r q) := hsimple
    exact CFSGOrthogonalDSerreMatrices.typeD_even_card r q hr

def RemainingEvenOrderModelAfterOrthogonalD (i : CFSG.Index) : Prop :=
  RemainingEvenOrderModelAfterSymplectic i ∧ ¬ OrthogonalDIndex i

theorem evenOrder_model_or_remaining_after_orthogonalD (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬ IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelAfterOrthogonalD i := by
  by_cases hD : OrthogonalDIndex i
  · exact Or.inl (orthogonalDIndex_even_card i hD)
  rcases evenOrder_model_or_remaining_after_symplectic i hn with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hD⟩

theorem odd_order_solvable_of_cfsg_and_remaining_models_after_orthogonalD
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingEvenOrderModelAfterOrthogonalD i →
        Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_after_orthogonalD i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
