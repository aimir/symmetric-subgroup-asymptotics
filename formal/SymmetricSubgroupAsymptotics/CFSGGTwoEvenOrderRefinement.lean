import SymmetricSubgroupAsymptotics.CFSGOrthogonalBEvenOrderRefinement
import SymmetricSubgroupAsymptotics.CFSGGTwoModelEvenOrder

/-! Removes precisely the original untwisted G₂ branch from the remaining
even-order obligations. No twisted or other exceptional case is included. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

 def GTwoIndex : CFSG.Index→Prop
  | .G2 _ _=>True
  | _=>False

 theorem gTwoIndex_even_card (i : CFSG.Index) [IsSimpleGroup i.Model]
    (hi : GTwoIndex i) : Even (Nat.card i.Model) := by
  cases i <;> try contradiction
  case G2 q hq hsimple=>
    letI : IsSimpleGroup (CFSG.Models.G2 q) := hsimple
    exact CFSGGTwoSerreMatrices.typeGTwo_even_card q

 def RemainingEvenOrderModelAfterGTwo (i : CFSG.Index) : Prop :=
  RemainingEvenOrderModelAfterOrthogonalB i ∧ ¬GTwoIndex i

 theorem evenOrder_model_or_remaining_after_gTwo (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelAfterGTwo i := by
  by_cases hG : GTwoIndex i
  · exact Or.inl (gTwoIndex_even_card i hG)
  rcases evenOrder_model_or_remaining_after_orthogonalB i hn with h|h
  · exact Or.inl h
  · exact Or.inr ⟨h,hG⟩

 theorem odd_order_solvable_of_cfsg_and_remaining_models_after_gTwo
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀(i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model→RemainingEvenOrderModelAfterGTwo i→Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_after_gTwo i hn with h|h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
