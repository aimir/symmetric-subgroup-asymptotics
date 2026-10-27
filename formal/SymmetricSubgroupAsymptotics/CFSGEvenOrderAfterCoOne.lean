import SymmetricSubgroupAsymptotics.CFSGEvenOrderAfterCoThree
import SymmetricSubgroupAsymptotics.CFSGCoOneSelectedInvolutionPeriod

/-! Cumulative parity reduction preserving every previous closed branch.
Only actual Co1 is removed from the remaining even-model callback. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingEvenOrderModelAfterCoOne (i : CFSG.Index) : Prop :=
  RemainingEvenOrderModelAfterCoThree i ∧ i ≠ .sporadic .co1

theorem evenOrder_model_or_remaining_after_co1 (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelAfterCoOne i := by
  by_cases hm : i = .sporadic .co1
  · subst i
    exact Or.inl (CFSGCoOneSelectedInvolutionPeriod.even_card hn)
  · rcases evenOrder_model_or_remaining_after_co3 i hn with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h,hm⟩

theorem odd_order_solvable_of_cfsg_and_remaining_after_co1
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingEvenOrderModelAfterCoOne i →
        Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_after_co1 i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
