import SymmetricSubgroupAsymptotics.CFSGEvenOrderAfterSuz
import SymmetricSubgroupAsymptotics.CFSGHNSelectedRowBasisSwap

/-! Cumulative parity reduction preserving every branch through Suz.
Only actual HN is removed from the remaining even-model callback. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingEvenOrderModelAfterHN (i : CFSG.Index) : Prop :=
  RemainingEvenOrderModelAfterSuz i ∧ i ≠ .sporadic .hn

theorem evenOrder_model_or_remaining_after_hn (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelAfterHN i := by
  by_cases hm : i = .sporadic .hn
  · subst i
    exact Or.inl (CFSGHNSelectedRowBasisSwap.even_card hn)
  · rcases evenOrder_model_or_remaining_after_suz i hn with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h,hm⟩

theorem odd_order_solvable_of_cfsg_and_remaining_after_hn
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingEvenOrderModelAfterHN i →
        Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_after_hn i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
