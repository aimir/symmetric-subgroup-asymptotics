import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameOrderSixLocalCatalogue
import Mathlib.GroupTheory.PGroup

/-!
# Binary normal subgroups of the actual ternary local target

An order-three group or a noncommutative order-six group has trivial normal
binary subgroups. Consequently every onto local map kills any displayed
normal binary kernel in its source. The target and both original maps stay
unchanged; no chosen isomorphism to a replacement C3 or S3 is needed.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The exact two eligible local targets have no binary normal radical. -/
theorem binary_normal_eq_bot_of_ternary_local
    {C : Type*} [Group C] [Finite C]
    (hC : Nat.card C = 3 ∨ (Nat.card C = 6 ∧ ¬ IsMulCommutative C))
    (N : Subgroup C) [N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  obtain ⟨a, ha⟩ := hN.exists_card_eq
  have hdvd : 2 ^ a ∣ Nat.card C := by
    rw [← ha]
    exact N.card_subgroup_dvd_card
  have hcle : Nat.card C ≤ 6 := by rcases hC with h | ⟨h, _⟩ <;> omega
  have hpow : 2 ^ a ≤ 6 := (Nat.le_of_dvd Nat.card_pos hdvd).trans hcle
  have ha2 : a ≤ 2 := by
    by_contra h
    have h3a : 3 ≤ a := by omega
    have h8 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) h3a
    norm_num at h8
    omega
  have hacases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases hacases with rfl | rfl | rfl
  · exact Subgroup.card_eq_one.mp (by simpa using ha)
  · have hcardN : Nat.card N = 2 := by simpa using ha
    rcases hC with hC | ⟨hC, hnoncomm⟩
    · norm_num [hC] at hdvd
    · have hquot : Nat.card (C ⧸ N) = 3 := by
        have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
        rw [hC, hcardN] at hmul
        omega
      exact False.elim
        (Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRowCatalogue.no_order_three_quotient_of_card_six_noncommutative
            hC hnoncomm (C ⧸ N) (QuotientGroup.mk' N)
            (QuotientGroup.mk'_surjective N) hquot)
  · rcases hC with h | ⟨h, _⟩ <;> norm_num [h] at hdvd

/-- An onto local map annihilates the displayed binary normal subgroup. -/
theorem binary_normal_le_kernel_of_ternary_local
    {H C : Type*} [Group H] [Group C] [Finite C]
    (f : H →* C) (hf : Function.Surjective f)
    (hC : Nat.card C = 3 ∨ (Nat.card C = 6 ∧ ¬ IsMulCommutative C))
    (N : Subgroup H) [N.Normal] (hN : IsPGroup 2 N) : N ≤ f.ker := by
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hbot := binary_normal_eq_bot_of_ternary_local hC (N.map f) (hN.map f)
  intro n hn
  have himage : f n ∈ N.map f := ⟨n, hn, rfl⟩
  rw [hbot] at himage
  exact himage

end SymmetricSubgroupAsymptotics

end
