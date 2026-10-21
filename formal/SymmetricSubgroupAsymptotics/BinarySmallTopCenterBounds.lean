import SymmetricSubgroupAsymptotics.CentralIndexFourDerivedBound

/-! A binary top of order at most32 and abelianization order at most8
has centre order at most4 unless it is abelian. This uses actual orders
and the central-index-four commutator theorem, not a group catalogue. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinarySmallTopCenterBounds

variable {B : Type} [Group B] [Finite B]

theorem center_le_four
    (hB : IsPGroup 2 B) (hcard : Nat.card B ≤ 32)
    (hAb : Nat.card (Abelianization B) ≤ 8)
    (hnonab : ¬ ∀ a b : B, a*b=b*a) :
    Nat.card (Subgroup.center B) ≤ 4 := by
  by_contra hn
  obtain ⟨z, hz⟩ := (hB.to_subgroup (Subgroup.center B)).exists_card_eq
  have hz3 : 3 ≤ z := by
    by_contra hz3
    have hzle : z ≤ 2 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hzle
    rw [← hz] at hp
    norm_num at hp
    omega
  have hz8 : 8 ≤ Nat.card (Subgroup.center B) := by
    rw [hz]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hz3
  have hi := SmallBinaryNormalFBounds.nonabelian_center_index_four_le hnonab
  have hc := (Subgroup.center B).card_mul_index
  have hm : 8 * (Subgroup.center B).index ≤ 32 :=
    (Nat.mul_le_mul_right _ hz8).trans (hc.le.trans hcard)
  have hi4 : (Subgroup.center B).index = 4 := by omega
  have hd := CentralIndexFourDerivedBound.commutator_card_le_two_of_center_index_four hi4 hnonab
  have hg := (commutator B).card_eq_card_quotient_mul_card_subgroup
  change Nat.card B = Nat.card (Abelianization B) * Nat.card (commutator B) at hg
  have hsmall : Nat.card B ≤ 16 := by nlinarith
  rw [hi4] at hc
  nlinarith

end SymmetricSubgroupAsymptotics.BinarySmallTopCenterBounds
