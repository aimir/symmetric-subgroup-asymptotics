import SymmetricSubgroupAsymptotics.CFSGEvenOrderAfterLy
import SymmetricSubgroupAsymptotics.CFSGMonsterSelectedDerivedInvolution

/-! Cumulative parity reduction preserving every branch through Ly/Th/ON.
Only actual Monster is removed from the remaining even-model callback. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingEvenOrderModelAfterMonster (i : CFSG.Index) : Prop :=
  RemainingEvenOrderModelAfterLy i ∧ i ≠ .sporadic .monster

theorem evenOrder_model_or_remaining_after_monster (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelAfterMonster i := by
  by_cases hm : i = .sporadic .monster
  · subst i
    exact Or.inl (CFSGMonsterSelectedDerivedInvolution.even_card hn)
  · rcases evenOrder_model_or_remaining_after_ly i hn with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h,hm⟩

theorem odd_order_solvable_of_cfsg_and_remaining_after_monster
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingEvenOrderModelAfterMonster i →
        Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_after_monster i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
