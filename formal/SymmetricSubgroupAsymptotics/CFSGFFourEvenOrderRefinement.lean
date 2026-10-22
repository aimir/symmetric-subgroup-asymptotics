import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckEvenOrderRefinement
import SymmetricSubgroupAsymptotics.CFSGFFourModelEvenOrder

/-! Removes precisely the original untwisted F4 branch. The remaining
pinned twisted and other exceptional model obligations stay explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def FFourIndex : CFSG.Index→Prop
  | .F4 _=>True
  | _=>False

theorem fFourIndex_even_card (i : CFSG.Index) [IsSimpleGroup i.Model]
    (hi : FFourIndex i) : Even (Nat.card i.Model) := by
  cases i <;> try contradiction
  case F4 q hsimple=>
    letI : IsSimpleGroup (CFSG.Models.F4 q) := hsimple
    exact CFSGFFourSerreMatrices.typeFFour_even_card q

def RemainingEvenOrderModelAfterFFour (i : CFSG.Index) : Prop :=
  RemainingEvenOrderModelAfterExceptionalE i ∧ ¬FFourIndex i

theorem evenOrder_model_or_remaining_after_fFour (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelAfterFFour i := by
  by_cases hF : FFourIndex i
  · exact Or.inl (fFourIndex_even_card i hF)
  rcases evenOrder_model_or_remaining_after_exceptionalE i hn with h|h
  · exact Or.inl h
  · exact Or.inr ⟨h,hF⟩

theorem odd_order_solvable_of_cfsg_and_remaining_models_after_fFour
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀(i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model→RemainingEvenOrderModelAfterFFour i→Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_after_fFour i hn with h|h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
