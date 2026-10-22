import SymmetricSubgroupAsymptotics.CFSGGTwoEvenOrderRefinement
import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckModelEvenOrder

/-! Removes precisely the original untwisted E6/E7/E8 branches from the
remaining even-order obligations. Twisted exceptional cases stay explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def ExceptionalEIndex : CFSG.Index→Prop
  | .E6 _ | .E7 _ | .E8 _=>True
  | _=>False

theorem exceptionalEIndex_even_card (i : CFSG.Index) [IsSimpleGroup i.Model]
    (hi : ExceptionalEIndex i) : Even (Nat.card i.Model) := by
  cases i <;> try contradiction
  case E6 q hsimple=>
    letI : IsSimpleGroup (CFSG.Models.E6 q) := hsimple
    exact CFSGExceptionalGeckModelEvenOrder.typeE6_even_card q
  case E7 q hsimple=>
    letI : IsSimpleGroup (CFSG.Models.E7 q) := hsimple
    exact CFSGExceptionalGeckModelEvenOrder.typeE7_even_card q
  case E8 q hsimple=>
    letI : IsSimpleGroup (CFSG.Models.E8 q) := hsimple
    exact CFSGExceptionalGeckModelEvenOrder.typeE8_even_card q

def RemainingEvenOrderModelAfterExceptionalE (i : CFSG.Index) : Prop :=
  RemainingEvenOrderModelAfterGTwo i ∧ ¬ExceptionalEIndex i

theorem evenOrder_model_or_remaining_after_exceptionalE (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelAfterExceptionalE i := by
  by_cases hE : ExceptionalEIndex i
  · exact Or.inl (exceptionalEIndex_even_card i hE)
  rcases evenOrder_model_or_remaining_after_gTwo i hn with h|h
  · exact Or.inl h
  · exact Or.inr ⟨h,hE⟩

theorem odd_order_solvable_of_cfsg_and_remaining_models_after_exceptionalE
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀(i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model→RemainingEvenOrderModelAfterExceptionalE i→Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_after_exceptionalE i hn with h|h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
