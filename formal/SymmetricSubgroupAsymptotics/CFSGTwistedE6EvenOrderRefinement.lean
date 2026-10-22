import SymmetricSubgroupAsymptotics.CFSGFFourEvenOrderRefinement
import SymmetricSubgroupAsymptotics.CFSGTwistedE6ModelEvenOrder

/-! Removes precisely the actual original twisted E6 branch after both
characteristics have been proved. Other model obligations remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def TwistedE6Index : CFSG.Index→Prop
  | .twistedE6 _=>True
  | _=>False

theorem twistedE6Index_even_card (i : CFSG.Index) [IsSimpleGroup i.Model]
    (hi : TwistedE6Index i) : Even (Nat.card i.Model) := by
  cases i <;> try contradiction
  case twistedE6 q hsimple=>
    letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := hsimple
    exact CFSGTwistedE6FixedA2.twistedE6_even_card q

def RemainingEvenOrderModelAfterTwistedE6 (i : CFSG.Index) : Prop :=
  RemainingEvenOrderModelAfterFFour i ∧ ¬TwistedE6Index i

theorem evenOrder_model_or_remaining_after_twistedE6 (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelAfterTwistedE6 i := by
  by_cases hE : TwistedE6Index i
  · exact Or.inl (twistedE6Index_even_card i hE)
  rcases evenOrder_model_or_remaining_after_fFour i hn with h|h
  · exact Or.inl h
  · exact Or.inr ⟨h,hE⟩

theorem odd_order_solvable_of_cfsg_and_remaining_models_after_twistedE6
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀(i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model→RemainingEvenOrderModelAfterTwistedE6 i→Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_after_twistedE6 i hn with h|h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
