import SymmetricSubgroupAsymptotics.CFSGEvenOrderRemainingModels
import SymmetricSubgroupAsymptotics.CFSGPresentedSporadicEvenOrder
import SymmetricSubgroupAsymptotics.CFSGAdditionalSporadicEvenOrder
import SymmetricSubgroupAsymptotics.CFSGYSectionEvenOrder

/-! Seventeen concrete sporadic parity branches are discharged by common
involution/presentation arguments. The eight matrix models and Monster
remain explicit. This is a refined reduction, not a CFSG-only proof of
odd-order solvability. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def SporadicEvenOrderResidual : CFSG.Sporadic → Prop
  | .co1 | .co3 | .ru | .suz | .onan | .hn | .ly | .th | .monster => True
  | _ => False

theorem sporadic_even_or_remaining (s : CFSG.Sporadic)
    (hn : ¬ IsMulCommutative s.Model) :
    Even (Nat.card s.Model) ∨ SporadicEvenOrderResidual s := by
  cases s with
  | m11 => exact Or.inl (m11_even_card hn)
  | m12 => exact Or.inl (m12_even_card hn)
  | m22 => exact Or.inl (mathieu22_even_card)
  | m23 => exact Or.inl (m23_even_card hn)
  | m24 => exact Or.inl (m24_even_card hn)
  | j1 => exact Or.inl (j1_even_card hn)
  | j2 => exact Or.inl (j2_even_card hn)
  | j3 => exact Or.inl (j3_even_card hn)
  | j4 => exact Or.inl (j4_even_card hn)
  | co1 => exact Or.inr trivial
  | co2 => exact Or.inl (co2_even_card hn)
  | co3 => exact Or.inr trivial
  | fi22 => exact Or.inl (y_simpleSection_even_card CFSG.Models.YGroups.arms332 hn)
  | fi23 => exact Or.inl (y_simpleSection_even_card CFSG.Models.YGroups.arms432 hn)
  | fi24Prime => exact Or.inl (y_simpleSection_even_card CFSG.Models.YGroups.arms442 hn)
  | hs => exact Or.inl (hs_even_card hn)
  | mcl => exact Or.inl (mcl_even_card hn)
  | he => exact Or.inl (he_even_card hn)
  | ru => exact Or.inr trivial
  | suz => exact Or.inr trivial
  | onan => exact Or.inr trivial
  | hn => exact Or.inr trivial
  | ly => exact Or.inr trivial
  | th => exact Or.inr trivial
  | babyMonster => exact Or.inl (y_simpleSection_even_card CFSG.Models.YGroups.arms433 hn)
  | monster => exact Or.inr trivial

def RemainingEvenOrderModelWithSporadics : CFSG.Index → Prop
  | .sporadic s => SporadicEvenOrderResidual s
  | i => RemainingEvenOrderModel i

theorem evenOrder_model_or_remaining_with_sporadics (i : CFSG.Index)
    (hn : ¬ IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelWithSporadics i := by
  cases i <;> try exact evenOrder_model_or_remaining _ hn
  case sporadic s => exact sporadic_even_or_remaining s hn

theorem odd_order_solvable_of_cfsg_and_remaining_models_with_sporadics
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingEvenOrderModelWithSporadics i →
        Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_with_sporadics i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
