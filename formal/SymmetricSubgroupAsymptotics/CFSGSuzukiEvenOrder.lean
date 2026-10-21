import SymmetricSubgroupAsymptotics.CFSGSuzukiTorusElements
import SymmetricSubgroupAsymptotics.CFSGSporadicEvenOrderRefinement

/-! The original Suzuki Weyl matrix is a nontrivial involution. This
removes Suzuki from the actual-model parity frontier without invoking
the order formula or odd-order solvability. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGSuzukiTorus

theorem suzuki_even_card (m : ℕ) : Even (Nat.card (CFSG.Models.Suzuki m)) := by
  by_contra he
  have ho : Odd (Nat.card (CFSG.Models.Suzuki m)) := Nat.not_even_iff_odd.mp he
  let x : CFSG.Models.Suzuki m := ⟨weylElement m,weylElement_mem_model m⟩
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    change weylElement m ^ 2 = 1
    simpa only [pow_two] using weylElement_square m
  have hx := eq_one_of_square_eq_one_of_odd_card ho x hx2
  have hm : weylElement m = 1 := congrArg Subtype.val hx
  have hv := congrArg (fun g : Ambient m =>
    (g : CFSG.Models.SuzukiConstruction.Mat m) 0 3) hm
  simpa [weylElement_coe,CFSG.Models.SuzukiConstruction.weyl] using hv

def RemainingEvenOrderModelWithoutSuzuki : CFSG.Index → Prop
  | .suzuki _ _ => False
  | i => RemainingEvenOrderModelWithSporadics i

theorem evenOrder_model_or_remaining_without_suzuki (i : CFSG.Index)
    (hn : ¬ IsMulCommutative i.Model) :
    Even (Nat.card i.Model) ∨ RemainingEvenOrderModelWithoutSuzuki i := by
  cases i <;> try exact evenOrder_model_or_remaining_with_sporadics _ hn
  case suzuki m hm => exact Or.inl (suzuki_even_card m)

theorem odd_order_solvable_of_cfsg_and_remaining_models_without_suzuki
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingEvenOrderModelWithoutSuzuki i →
        Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  rcases evenOrder_model_or_remaining_without_suzuki i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
