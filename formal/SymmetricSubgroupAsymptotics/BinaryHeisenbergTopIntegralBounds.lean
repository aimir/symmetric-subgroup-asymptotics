import SymmetricSubgroupAsymptotics.BinaryHeisenbergTopCentralCore
import SymmetricSubgroupAsymptotics.NormalIntegralCardCenterBound

/-! Actual Heisenberg-top integral bounds use its two-element original
center. No quotient-generator count replaces an integral order. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergTopIntegralBounds
open BinaryHeisenbergEightNaturalHeads

theorem center_card_le_two : Nat.card (Subgroup.center H) ≤ 2 := by
  classical
  let f : Subgroup.center H → Fin 2 := fun x => if x.val = 1 then 0 else 1
  have hf : Function.Injective f := by
    intro x y h
    by_cases hx : x.val = 1
    · have hy : y.val = 1 := by
        by_contra hn
        simp only [f, if_pos hx, if_neg hn] at h
        exact (by decide : (0 : Fin 2) ≠ 1) h
      exact Subtype.ext (hx.trans hy.symm)
    · have hy : y.val ≠ 1 := by
        intro hy
        simp only [f, if_neg hx, if_pos hy] at h
        exact (by decide : (1 : Fin 2) ≠ 0) h
      have hxz := (BinaryHeisenbergTopCentralCore.central_cases x.val x.property).resolve_left hx
      have hyz := (BinaryHeisenbergTopCentralCore.central_cases y.val y.property).resolve_left hy
      exact Subtype.ext (hxz.trans hyz.symm)
  exact (Nat.card_le_card_of_injective f hf).trans_eq (Nat.card_fin 2)

theorem proper_normal_integral_order_le_eight
    (T : Subgroup H) [T.Normal] (hT : T ≠ ⊤) :
    normalIntegralCoinvariantOrder T ≤ 8 := by
  have hi := T.one_lt_index_of_ne_top hT
  have hc := T.card_mul_index
  rw [BinaryMenuCayley8T22.exact_card] at hc
  apply normalIntegralCoinvariantOrder_le_of_card_center T 8 (by nlinarith)
  exact center_card_le_two.trans (by decide)

theorem normal_integral_order_le_four_of_card_le_eight
    (T : Subgroup H) [T.Normal] (hT : Nat.card T ≤ 8) :
    normalIntegralCoinvariantOrder T ≤ 4 :=
  normalIntegralCoinvariantOrder_le_of_card_center T 4 hT
    (center_card_le_two.trans (by decide))

end SymmetricSubgroupAsymptotics.BinaryHeisenbergTopIntegralBounds
