import SymmetricSubgroupAsymptotics.BinaryTargetOrderEnvelope
import SymmetricSubgroupAsymptotics.ScalarFourCentralColdEnvelope
import SymmetricSubgroupAsymptotics.PermutationThreeGroupRank
import Mathlib.Algebra.Group.TypeTags.Finite

/-! The killed-top branch pays every source without a hot exception. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {H : Type} [Group H] [Finite H]

theorem small_binary_quotient_epi_envelope_two (r : ℕ) (hr : r≤2)
    (e : H ≃* (Fin r → Multiplicative (ZMod 2)))
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J H) : ℝ)≤(2 : ℝ)^((1 : ℝ)*(b : ℝ)) := by
  letI : Finite (J →* H) := Finite.of_injective
    (fun f : J →* H => (f : J → H)) DFunLike.coe_injective
  have hH : Nat.card H=2^r := by
    rw [Nat.card_congr e.toEquiv,Nat.card_fun,Nat.card_congr Multiplicative.toAdd]
    simp
  have hc : Nat.card (GroupEpimorphism J H)≤2^(r*binaryCharacterRank J) :=
    (Nat.card_le_card_of_injective (fun x : GroupEpimorphism J H => x.val)
      Subtype.val_injective).trans (binaryTargetOrder_hom_card_le_of_card_pow_two r hH)
  have hk := permutation_binaryCharacterRank_le_half J (Fin b)
  rw [Nat.card_fin] at hk
  change binaryCharacterRank J≤b/2 at hk
  have hexp : ((r*binaryCharacterRank J : ℕ) : ℝ)≤(1 : ℝ)*(b : ℝ) := by
    have hn : 2*(r*binaryCharacterRank J)≤2*b := by nlinarith [Nat.div_mul_le_self b 2]
    have hn' : (2 : ℝ)*((r*binaryCharacterRank J : ℕ) : ℝ)≤2*(b : ℝ) := by
      exact_mod_cast hn
    linarith
  have hc' : (Nat.card (GroupEpimorphism J H) : ℝ)≤
      (2 : ℝ)^((r*binaryCharacterRank J : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hc
  exact hc'.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) hexp)

end SymmetricSubgroupAsymptotics
