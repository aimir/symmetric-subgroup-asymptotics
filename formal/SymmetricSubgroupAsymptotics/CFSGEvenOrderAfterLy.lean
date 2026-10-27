import SymmetricSubgroupAsymptotics.CFSGEvenOrderAfterTh
import SymmetricSubgroupAsymptotics.CFSGLySelectedRowCombination

/-! Cumulative parity reduction preserving every branch through Th/ON/HN.
Only actual Ly is removed from the remaining even-model callback. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingEvenOrderModelAfterLy (i : CFSG.Index) : Prop :=
  RemainingEvenOrderModelAfterTh i ∧ i ≠ .sporadic .ly

theorem evenOrder_model_or_remaining_after_ly (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelAfterLy i := by
  by_cases hm : i = .sporadic .ly
  · subst i
    exact Or.inl (CFSGLySelectedRowCombination.even_card hn)
  · rcases evenOrder_model_or_remaining_after_th i hn with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h,hm⟩

theorem odd_order_solvable_of_cfsg_and_remaining_after_ly
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingEvenOrderModelAfterLy i →
        Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_after_ly i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
