import SymmetricSubgroupAsymptotics.CFSGSerreCharacteristicTwoParity
import SymmetricSubgroupAsymptotics.CFSGSporadicEvenOrderRefinement
import SymmetricSubgroupAsymptotics.CFSGSuzukiEvenOrder

/-! The literal untwisted Serre models in characteristic two need no
classical-group identification for parity. This refines the existing
alternating/type-A/seventeen-sporadic/Suzuki reduction; other cases stay
explicit, so no full odd-order theorem is asserted here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem primePower_serre_projective_even {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (q : CFSG.PrimePower) (hq : q.prime = 2)
    [Nontrivial (CFSG.Models.Chevalley.Projective A q.Field)] :
    Even (Nat.card (CFSG.Models.Chevalley.Projective A q.Field)) := by
  letI : CharP q.Field 2 := by rw [← hq]; infer_instance
  exact CFSGSerreCharacteristicTwoParity.projective_even_card A q.Field

def CharacteristicTwoUntwistedIndex : CFSG.Index → Prop
  | .B _ q _ | .C _ q _ _ | .D _ q _ | .E6 q | .E7 q | .E8 q | .F4 q | .G2 q _ =>
    q.prime = 2
  | _ => False

theorem characteristicTwoUntwisted_even_card (i : CFSG.Index) [Nontrivial i.Model]
    (hi : CharacteristicTwoUntwistedIndex i) : Even (Nat.card i.Model) := by
  cases i <;> try contradiction
  case B r q _ hnt =>
    letI : Nontrivial (CFSG.Models.B r q) := hnt
    exact primePower_serre_projective_even (CartanMatrix.B r).transpose q hi
  case C r q _ _ hnt =>
    letI : Nontrivial (CFSG.Models.C r q) := hnt
    exact primePower_serre_projective_even (CartanMatrix.C r).transpose q hi
  case D r q _ hnt =>
    letI : Nontrivial (CFSG.Models.D r q) := hnt
    exact primePower_serre_projective_even (CartanMatrix.D r) q hi
  case E6 q hnt =>
    letI : Nontrivial (CFSG.Models.E6 q) := hnt
    exact primePower_serre_projective_even CartanMatrix.E₆ q hi
  case E7 q hnt =>
    letI : Nontrivial (CFSG.Models.E7 q) := hnt
    exact primePower_serre_projective_even CartanMatrix.E₇ q hi
  case E8 q hnt =>
    letI : Nontrivial (CFSG.Models.E8 q) := hnt
    exact primePower_serre_projective_even CartanMatrix.E₈ q hi
  case F4 q hnt =>
    letI : Nontrivial (CFSG.Models.F4 q) := hnt
    exact primePower_serre_projective_even CartanMatrix.F₄ q hi
  case G2 q _ hnt =>
    letI : Nontrivial (CFSG.Models.G2 q) := hnt
    exact primePower_serre_projective_even CartanMatrix.G₂ q hi

def RemainingEvenOrderModelAfterSerreTwo (i : CFSG.Index) : Prop :=
  RemainingEvenOrderModelWithSporadics i ∧
    RemainingEvenOrderModelWithoutSuzuki i ∧ ¬ CharacteristicTwoUntwistedIndex i

theorem evenOrder_model_or_remaining_after_serre_two (i : CFSG.Index)
    [Nontrivial i.Model] (hn : ¬ IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelAfterSerreTwo i := by
  by_cases htwo : CharacteristicTwoUntwistedIndex i
  · exact Or.inl (characteristicTwoUntwisted_even_card i htwo)
  rcases evenOrder_model_or_remaining_with_sporadics i hn with h | hsporadic
  · exact Or.inl h
  rcases evenOrder_model_or_remaining_without_suzuki i hn with h | hsuzuki
  · exact Or.inl h
  · exact Or.inr ⟨hsporadic, hsuzuki, htwo⟩

theorem odd_order_solvable_of_cfsg_and_remaining_models_after_serre_two
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingEvenOrderModelAfterSerreTwo i →
        Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_after_serre_two i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
