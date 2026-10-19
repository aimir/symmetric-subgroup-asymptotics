import SymmetricSubgroupAsymptotics.BinaryKernelRankTailNumerics
import SymmetricSubgroupAsymptotics.FiniteTopKernelRankHotTail

/-! Every binary target with a fixed order exponent has a complete
source-summed bound. The cold rank test is on the same complete source;
the hot term retains every epimorphism. Non-elementary targets are allowed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace BinaryTargetRankTailSum
variable {H : Type} [Group H] [Finite H]

private theorem rank_bound (r : ℕ) (hcard : Nat.card H=2^r)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    Nat.card (GroupEpimorphism J H)≤2^(r*binaryCharacterRank J) := by
  letI : Finite (J →* H) := Finite.of_injective
    (fun f : J →* H => (f : J → H)) DFunLike.coe_injective
  exact (Nat.card_le_card_of_injective
    (fun f : GroupEpimorphism J H => f.val) Subtype.val_injective).trans
      (binaryTargetOrder_hom_card_le_of_card_pow_two r hcard)

theorem cold_epi_le (m r : ℕ) (hr : r≤ m) (hcard : Nat.card H=2^r)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬BinaryRankHot (51/200) J) :
    (Nat.card (GroupEpimorphism J H) : ℝ)≤(2 : ℝ)^(((m : ℝ)*(51/200))*b) := by
  have hc : (Nat.card (GroupEpimorphism J H) : ℝ)≤
      (2 : ℝ)^((r*binaryCharacterRank J : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast rank_bound r hcard J
  have hhot : (binaryCharacterRank J : ℝ)≤(51/200 : ℝ)*b := le_of_not_gt hJ
  have hrR : (r : ℝ)≤ m := by exact_mod_cast hr
  have he : ((r*binaryCharacterRank J : ℕ) : ℝ)≤((m : ℝ)*(51/200))*b := by
    push_cast
    have h1 := mul_le_mul_of_nonneg_right hrR
      (show 0≤(binaryCharacterRank J : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hhot
      (show 0≤(m : ℝ) by positivity)
    nlinarith
  exact hc.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) he)

theorem full_sum_le (m r : ℕ) (hr : r≤ m) (hcard : Nat.card H=2^r) (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J H) : ℝ)) ≤
      BinaryKernelRankTailNumerics.raw 1 m b+
        (subgroupCount b : ℝ)*(2 : ℝ)^(((m : ℝ)*(51/200))*b) := by
  let hot : Subgroup (Equiv.Perm (Fin b)) → Prop := BinaryRankHot (51/200)
  have hH : Nat.card H≤2^m := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide : 1≤2) hr
  have hh : (∑ J ∈ Finset.univ.filter hot,
      (Nat.card (GroupEpimorphism J H) : ℝ))≤BinaryKernelRankTailNumerics.raw 1 m b := by
    calc
      _ ≤ ∑ _J ∈ Finset.univ.filter hot,(Nat.factorial b : ℝ)^m := by
        apply Finset.sum_le_sum
        intro J _
        exact_mod_cast groupEpimorphism_card_le_factorial_pow J hH
      _ = ((Finset.univ.filter hot).card : ℝ)*(Nat.factorial b : ℝ)^m := by
        rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ ((2 : ℝ)^(-((rankTail51Tilt b : ℝ)*(51/200)*b))*
          (subgroupCount (b+2*rankTail51Tilt b) : ℝ))*(Nat.factorial b : ℝ)^m :=
        mul_le_mul_of_nonneg_right (binaryRankHot51_card_le b) (by positivity)
      _ = _ := by unfold BinaryKernelRankTailNumerics.raw; ring
  have hc : (∑ J ∈ Finset.univ.filter (fun J => ¬hot J),
      (Nat.card (GroupEpimorphism J H) : ℝ))≤
        (subgroupCount b : ℝ)*(2 : ℝ)^(((m : ℝ)*(51/200))*b) := by
    calc
      _ ≤ ∑ _J ∈ Finset.univ.filter (fun J => ¬hot J),(2 : ℝ)^(((m : ℝ)*(51/200))*b) := by
        apply Finset.sum_le_sum
        intro J hJ
        exact cold_epi_le m r hr hcard b J (Finset.mem_filter.mp hJ).2
      _ ≤ ∑ _J : Subgroup (Equiv.Perm (Fin b)),(2 : ℝ)^(((m : ℝ)*(51/200))*b) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
      _ = _ := by simp [subgroupCount]
  rw [←Finset.sum_filter_add_sum_filter_not Finset.univ hot]
  exact add_le_add hh hc

end BinaryTargetRankTailSum
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
