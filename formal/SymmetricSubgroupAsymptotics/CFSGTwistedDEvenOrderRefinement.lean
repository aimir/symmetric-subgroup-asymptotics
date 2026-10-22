import SymmetricSubgroupAsymptotics.CFSGTwistedE6EvenOrderRefinement
import SymmetricSubgroupAsymptotics.CFSGTwistedDImageParity

/-! Precisely the original twisted-D tags leave the parity residual,
uniformly in rank and characteristic. Every other remaining model and
the final classification premise remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def TwistedDIndex : CFSG.Index → Prop
  | .twistedD _ _ _ => True
  | _ => False

theorem twistedDIndex_even_card (i : CFSG.Index) [IsSimpleGroup i.Model]
    (hi : TwistedDIndex i) : Even (Nat.card i.Model) := by
  cases i <;> try contradiction
  case twistedD r q hr hsimple =>
    letI : IsSimpleGroup (CFSG.Models.TwistedD r q) := hsimple
    exact CFSGTwistedDFixedA2.twistedD_even_card r hr q

def RemainingEvenOrderModelAfterTwistedD (i : CFSG.Index) : Prop :=
  RemainingEvenOrderModelAfterTwistedE6 i ∧ ¬TwistedDIndex i

theorem evenOrder_model_or_remaining_after_twistedD (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelAfterTwistedD i := by
  by_cases hD : TwistedDIndex i
  · exact Or.inl (twistedDIndex_even_card i hD)
  rcases evenOrder_model_or_remaining_after_twistedE6 i hn with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hD⟩

theorem odd_order_solvable_of_cfsg_and_remaining_models_after_twistedD
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingEvenOrderModelAfterTwistedD i → Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_after_twistedD i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
