import SymmetricSubgroupAsymptotics.SmallBinaryNormalIntegralCoinvariants
import SymmetricSubgroupAsymptotics.NormalIntegralCardCenterBound
import SymmetricSubgroupAsymptotics.RelativeIntegralIndexFour
import SymmetricSubgroupAsymptotics.FaithfulTransitiveCentralCard

/-! A sixty-four-element binary top has small integral relative quotients
once its actual center and abelianization are small. The center hypothesis
is proved automatically for nonregular faithful transitive degree eight. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {H : Type} [Group H] [Finite H]

theorem binary_proper_normal_integral_order_le_four_of_card_le_sixtyfour
    (hH : IsPGroup 2 H) (hcard : Nat.card H ≤ 64)
    (hAb : Nat.card (Abelianization H) ≤ 8)
    (hcenter : Nat.card (Subgroup.center H) ≤ 4)
    (T : Subgroup H) [T.Normal] (hproper : T ≠ ⊤) :
    normalIntegralCoinvariantOrder T ≤ 4 := by
  letI binarySixtyFourIntegral_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases htwo : T.index = 2
  · letI binarySixtyFourIntegral_cyclic : IsCyclic (H ⧸ T) := isCyclic_of_prime_card htwo
    have he := relative_integral_order_mul_index_of_cyclic_quotient T
    rw [htwo] at he
    change (⁅T, (⊤ : Subgroup H)⁆).relIndex T ≤ 4
    omega
  by_cases hfour : T.index = 4
  · have he := normalIntegralCoinvariantOrder_double_le_abelianization_of_index_four T hfour
    omega
  have hindex : 8 ≤ T.index := by
    obtain ⟨k, hk⟩ := (hH.to_quotient T).exists_card_eq
    change T.index = 2 ^ k at hk
    have hproperIndex := T.one_lt_index_of_ne_top hproper
    have hk3 : 3 ≤ k := by
      by_contra hn
      have hkcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hkcases with rfl | rfl | rfl
      · change T.index = 1 at hk
        omega
      · change T.index = 2 at hk
        exact htwo hk
      · change T.index = 4 at hk
        exact hfour hk
    rw [hk]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hk3
  have hTcard : Nat.card T ≤ 8 := by
    have he := T.card_mul_index
    have hm := Nat.mul_le_mul_left (Nat.card T) hindex
    rw [he] at hm
    omega
  exact normalIntegralCoinvariantOrder_le_of_card_center T 4 hTcard hcenter

/-- The actual transitive degree-eight action rules out a center of
order eight whenever the original top is larger than a regular group. -/
theorem transitive_binary_degree_eight_center_card_le_four
    (H : Subgroup (Equiv.Perm (Fin 8))) [MulAction.IsPretransitive H (Fin 8)]
    (hH : IsPGroup 2 H) (hlarge : 8 < Nat.card H) :
    Nat.card (Subgroup.center H) ≤ 4 := by
  have hc : Nat.card (Subgroup.center H) < 8 := by
    simpa only [Nat.card_fin] using central_card_lt_points_of_points_lt_group
      (Subgroup.center H).subtype Subtype.val_injective (fun z => z.property)
      (0 : Fin 8) (by simpa only [Nat.card_fin] using hlarge)
  obtain ⟨z, hz⟩ := (hH.to_subgroup (Subgroup.center H)).exists_card_eq
  have hz2 : z ≤ 2 := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 3 ≤ z by omega)
    rw [← hz] at hp
    norm_num at hp
    omega
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hz2
  rw [← hz] at hp
  exact hp

end SymmetricSubgroupAsymptotics
