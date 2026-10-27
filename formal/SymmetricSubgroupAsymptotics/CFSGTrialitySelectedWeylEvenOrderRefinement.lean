import SymmetricSubgroupAsymptotics.CFSGTwistedAReversalEvenOrderRefinement
import SymmetricSubgroupAsymptotics.CFSGTrialitySelectedWeylEvenOrder

/-! Exactly the original triality-D4 tag leaves the parity callback.
All previous closures are retained; the only simple-group instance used
by the new branch is the same inherited original-model instance. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def TrialityParityIndex : CFSG.Index → Prop
  | .trialityD4 _ => True
  | _ => False

theorem trialityParityIndex_even_card (i : CFSG.Index) [IsSimpleGroup i.Model]
    (hi : TrialityParityIndex i) : Even (Nat.card i.Model) := by
  cases i <;> try contradiction
  case trialityD4 q hsimple =>
    letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := hsimple
    exact CFSGTrialitySelectedWeylEvenOrder.triality_even_card q

def RemainingEvenOrderModelAfterTrialityParity (i : CFSG.Index) : Prop :=
  RemainingEvenOrderModelAfterTwistedAReversal i ∧ ¬TrialityParityIndex i

theorem evenOrder_model_or_remaining_after_triality_parity (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelAfterTrialityParity i := by
  by_cases hi : TrialityParityIndex i
  · exact Or.inl (trialityParityIndex_even_card i hi)
  · rcases evenOrder_model_or_remaining_after_twistedA_reversal i hn with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h,hi⟩

theorem odd_order_solvable_of_cfsg_and_remaining_after_triality_parity
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingEvenOrderModelAfterTrialityParity i →
        Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_after_triality_parity i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
