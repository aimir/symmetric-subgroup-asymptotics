import SymmetricSubgroupAsymptotics.CFSGReeAndTitsEvenOrderRefinement
import SymmetricSubgroupAsymptotics.CFSGTwistedAReversalEvenOrder

/-! Exactly the original twisted-A tag leaves the parity callback;
all previous sporadic/Ree/Tits closures and the rank2 guard are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def TwistedAReversalIndex : CFSG.Index → Prop
  | .twistedA _ _ _ _ => True
  | _ => False

theorem twistedAReversalIndex_even_card (i : CFSG.Index) (hi : TwistedAReversalIndex i) :
    Even (Nat.card i.Model) := by
  cases i <;> try contradiction
  case twistedA r q hr hsmall =>
    exact CFSGTwistedAReversalEvenOrder.twistedA_even_card r hr q hsmall

def RemainingEvenOrderModelAfterTwistedAReversal (i : CFSG.Index) : Prop :=
  RemainingEvenOrderModelAfterReeAndTits i ∧ ¬TwistedAReversalIndex i

theorem evenOrder_model_or_remaining_after_twistedA_reversal (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelAfterTwistedAReversal i := by
  by_cases hi : TwistedAReversalIndex i
  · exact Or.inl (twistedAReversalIndex_even_card i hi)
  · rcases evenOrder_model_or_remaining_after_ree_and_tits i hn with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h,hi⟩

theorem odd_order_solvable_of_cfsg_and_remaining_after_twistedA_reversal
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingEvenOrderModelAfterTwistedAReversal i →
        Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_after_twistedA_reversal i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
