import SymmetricSubgroupAsymptotics.CFSGEvenOrderAfterHN
import SymmetricSubgroupAsymptotics.CFSGONSelectedRowBasisSwap

/-! Cumulative parity reduction preserving every branch through HN/Suz.
Only actual ON is removed from the remaining even-model callback. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingEvenOrderModelAfterON (i : CFSG.Index) : Prop :=
  RemainingEvenOrderModelAfterHN i ∧ i ≠ .sporadic .onan

theorem evenOrder_model_or_remaining_after_on (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelAfterON i := by
  by_cases hm : i = .sporadic .onan
  · subst i
    exact Or.inl (CFSGONSelectedRowBasisSwap.even_card hn)
  · rcases evenOrder_model_or_remaining_after_hn i hn with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h,hm⟩

theorem odd_order_solvable_of_cfsg_and_remaining_after_on
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingEvenOrderModelAfterON i →
        Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_after_on i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
