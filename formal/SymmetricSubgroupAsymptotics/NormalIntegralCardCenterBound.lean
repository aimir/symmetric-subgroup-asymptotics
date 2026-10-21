import SymmetricSubgroupAsymptotics.NormalIntegralCoinvariantExtension

/-! A full integral relative quotient is paid either by a genuine
commutator bit or by the original ambient center. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G] [Finite G]

theorem normalIntegralCoinvariantOrder_le_of_card_center
    (N : Subgroup G) [N.Normal] (B : ℕ)
    (hcard : Nat.card N ≤ 2 * B)
    (hcenter : Nat.card (Subgroup.center G) ≤ B) :
    normalIntegralCoinvariantOrder N ≤ B := by
  let C := ⁅N, (⊤ : Subgroup G)⁆
  by_cases hzero : C = ⊥
  · have hcentral : N ≤ Subgroup.center G := by
      have hh := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero
      simpa only [Subgroup.coe_top, Subgroup.centralizer_univ] using hh
    change C.relIndex N ≤ B
    rw [hzero, Subgroup.relIndex_bot_left]
    exact (Subgroup.card_le_of_le hcentral).trans hcenter
  · have hc2 : 2 ≤ Nat.card C := C.one_lt_card_iff_ne_bot.mpr hzero
    have hc := (C.subgroupOf N).card_mul_index
    have he : Nat.card (C.subgroupOf N) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.commutator_le_left N (⊤ : Subgroup G))).toEquiv
    rw [he] at hc
    change C.relIndex N ≤ B
    have hmul : 2 * C.relIndex N ≤ 2 * B :=
      (Nat.mul_le_mul_right _ hc2).trans (hc.le.trans hcard)
    omega

end SymmetricSubgroupAsymptotics
