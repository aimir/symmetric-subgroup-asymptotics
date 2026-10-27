import SymmetricSubgroupAsymptotics.CFSGEvenOrderAfterMonster
import SymmetricSubgroupAsymptotics.CFSGReeGTwoSelectedDerivedInvolution
import SymmetricSubgroupAsymptotics.CFSGReeFFourAndTitsEvenOrder

/-! Remove exactly the two original Ree tags and Tits from the parity
callback, preserving all closures through Monster. Both actual full-centre
quotients are used. The remaining model callback is still explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def ReeAndTitsIndex : CFSG.Index → Prop
  | .reeG2 _ _ => True
  | .reeF4 _ _ => True
  | .tits => True
  | _ => False

theorem reeAndTitsIndex_even_card (i : CFSG.Index) (hi : ReeAndTitsIndex i) :
    Even (Nat.card i.Model) := by
  cases i <;> try contradiction
  case reeG2 m hm => exact CFSGReeGTwoSelectedDerivedInvolution.reeG2_even_card m hm
  case reeF4 m hm => exact CFSGReeFFourAndTitsEvenOrder.reeF4_even_card m
  case tits => exact CFSGReeFFourAndTitsEvenOrder.tits_even_card

def RemainingEvenOrderModelAfterReeAndTits (i : CFSG.Index) : Prop :=
  RemainingEvenOrderModelAfterMonster i ∧ ¬ReeAndTitsIndex i

theorem evenOrder_model_or_remaining_after_ree_and_tits (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelAfterReeAndTits i := by
  by_cases hi : ReeAndTitsIndex i
  · exact Or.inl (reeAndTitsIndex_even_card i hi)
  · rcases evenOrder_model_or_remaining_after_monster i hn with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h,hi⟩

theorem odd_order_solvable_of_cfsg_and_remaining_after_ree_and_tits
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingEvenOrderModelAfterReeAndTits i →
        Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_after_ree_and_tits i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
