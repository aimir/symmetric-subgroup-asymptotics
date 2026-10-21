import SymmetricSubgroupAsymptotics.BinaryNormalOrderFourSecondCenter

/-! An actual normal subgroup of order four contains the whole centre
when that centre has order at most two. The mixed commutator supplies the
nonzero central line; no normal-subgroup classification is involved. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics
variable {G : Type} [Group G] [Finite G]

theorem binary_normal_order_four_contains_center_of_card_le_two
    (hG : IsPGroup 2 G) (hcenter : Nat.card (Subgroup.center G)≤2)
    (L : Subgroup G) [L.Normal] (hcard : Nat.card L=4) :
    Subgroup.center G≤L := by
  let C := ⁅L,(⊤ : Subgroup G)⁆
  have hCZ : C≤Subgroup.center G := binary_normal_order_four_commutator_le_center hG L hcard
  have hCne : C≠⊥ := by
    intro he
    have hLZ : L≤Subgroup.center G := by
      intro l hl
      apply Subgroup.mem_center_iff.mpr
      intro g
      have hm : ⁅l,g⁆=1 := by
        apply Subgroup.mem_bot.mp
        rw [←he]
        exact Subgroup.commutator_mem_commutator hl (Subgroup.mem_top g)
      exact (commutatorElement_eq_one_iff_mul_comm.mp hm).symm
    have hc := (Subgroup.card_le_of_le hLZ).trans hcenter
    rw [hcard] at hc
    omega
  have hlow := C.one_lt_card_iff_ne_bot.mpr hCne
  have heq : C=Subgroup.center G :=
    Subgroup.eq_of_le_of_card_ge hCZ (by omega)
  rw [←heq]
  exact Subgroup.commutator_le_left L ⊤
end SymmetricSubgroupAsymptotics
