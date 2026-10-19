import SymmetricSubgroupAsymptotics.OriginalNormalAxisSourceEnvelope
import SymmetricSubgroupAsymptotics.MixedKernelRankTailPublishedSource
import SymmetricSubgroupAsymptotics.FiniteGroupPaddedGenerators

/-! A structural witness is required for EVERY original normal quotient.
A finite normal-locator table alone cannot supply this input. Each axis is
summed once, and its original raw epimorphism convention is preserved. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.OriginalNormalAxisSourceMenu
open Non2UnipotentPrefixFiniteMenu
variable {G : Type} [Group G] [Finite G]

theorem complete_sum_le (hG : Nat.card G≤2^15)
    (cover : ∀ (N : Subgroup G) [N.Normal], Choice (G ⧸ N))
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), completeQuotientWeight (R := G) J)≤
      (2 : ℝ)^(512 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
        (BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(225 : ℕ)) 21 b+
          MarkedC4KernelRankTailNumerics.raw ((2 : ℝ)^(225 : ℕ)) 21 b) := by
  have hN (N : {N : Subgroup G // N.Normal}) :
      (∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J (G ⧸ N.val)) : ℝ))≤
        (2 : ℝ)^(225 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
          (BinaryKernelRankTailNumerics.raw 1 21 b+MarkedC4KernelRankTailNumerics.raw 1 21 b) := by
    letI : N.val.Normal := N.property
    exact axis_sum_le ((Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective N.val)).trans hG)
      (cover N.val) hZmud lit b
  have hn : (Nat.card {N : Subgroup G // N.Normal} : ℝ)≤(2 : ℝ)^(225 : ℕ) := by
    exact_mod_cast normalSubgroup_card_le_two_pow_sq 15 hG
  have htotal :
      (∑ N : {N : Subgroup G // N.Normal},
        ∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J (G ⧸ N.val)) : ℝ))≤
      (Nat.card {N : Subgroup G // N.Normal} : ℝ)*
        ((2 : ℝ)^(225 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
          (BinaryKernelRankTailNumerics.raw 1 21 b+MarkedC4KernelRankTailNumerics.raw 1 21 b)) := by
    calc
      _ ≤ ∑ _N : {N : Subgroup G // N.Normal},
          ((2 : ℝ)^(225 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
            (BinaryKernelRankTailNumerics.raw 1 21 b+MarkedC4KernelRankTailNumerics.raw 1 21 b)) :=
        Finset.sum_le_sum (fun N _ => hN N)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_eq_nat_card]
  have hcold : (Nat.card {N : Subgroup G // N.Normal} : ℝ)*
      ((2 : ℝ)^(225 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ))≤
      (2 : ℝ)^(512 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ) := by
    have hp : (Nat.card {N : Subgroup G // N.Normal} : ℝ)*(2 : ℝ)^(225 : ℕ)≤(2 : ℝ)^(512 : ℕ) := by
      calc
        _ ≤ (2 : ℝ)^(225 : ℕ)*(2 : ℝ)^(225 : ℕ) := mul_le_mul_of_nonneg_right hn (by positivity)
        _ = (2 : ℝ)^(450 : ℕ) := by rw [←pow_add]
        _ ≤ (2 : ℝ)^(512 : ℕ) := pow_le_pow_right₀ (by norm_num) (by omega)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hp
      (show 0≤(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ) by positivity)
  have hbinary : (Nat.card {N : Subgroup G // N.Normal} : ℝ)*
      BinaryKernelRankTailNumerics.raw 1 21 b≤BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(225 : ℕ)) 21 b := by
    have hh := mul_le_mul_of_nonneg_right hn
      (show 0≤BinaryKernelRankTailNumerics.raw 1 21 b by unfold BinaryKernelRankTailNumerics.raw; positivity)
    simpa only [BinaryKernelRankTailNumerics.raw,one_mul,mul_assoc] using hh
  have hmarked : (Nat.card {N : Subgroup G // N.Normal} : ℝ)*
      MarkedC4KernelRankTailNumerics.raw 1 21 b≤MarkedC4KernelRankTailNumerics.raw ((2 : ℝ)^(225 : ℕ)) 21 b := by
    have hh := mul_le_mul_of_nonneg_right hn
      (show 0≤MarkedC4KernelRankTailNumerics.raw 1 21 b by
        unfold MarkedC4KernelRankTailNumerics.raw markedC4Moment; positivity)
    simpa only [MarkedC4KernelRankTailNumerics.raw,one_mul,mul_assoc] using hh
  have hbound := add_le_add hcold (add_le_add hbinary hmarked)
  have hsum : (∑ N : {N : Subgroup G // N.Normal},
      ∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J (G ⧸ N.val)) : ℝ))≤
      (2 : ℝ)^(512 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
        (BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(225 : ℕ)) 21 b+
          MarkedC4KernelRankTailNumerics.raw ((2 : ℝ)^(225 : ℕ)) 21 b) :=
    htotal.trans (by simpa only [mul_add] using hbound)
  unfold completeQuotientWeight completeQuotientCount
  simp only [Nat.cast_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ N : {N : Subgroup G // N.Normal},
        ∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J (G ⧸ N.val)) : ℝ) := by
      apply Finset.sum_congr
      · ext N; simp
      · intro N _; rfl
    _ ≤ _ := hsum

variable {U : PreE7NonPairActionClass 16}

def actualData (hU : Nat.card (preE7NonPairAction 16 U)≤2^15)
    (cover : ∀ (N : Subgroup (preE7NonPairAction 16 U)) [N.Normal],
      Choice (preE7NonPairAction 16 U ⧸ N))
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    MixedKernelRankTailResidual.Data 16 U where
  cold := (2 : ℝ)^(512 : ℕ)
  theta := 381/192
  hotBinary := (2 : ℝ)^(225 : ℕ)
  factorialPowerBinary := 21
  hotC4 := (2 : ℝ)^(225 : ℕ)
  factorialPowerC4 := 21
  cold_nonneg := by positivity
  hotBinary_nonneg := by positivity
  hotC4_nonneg := by positivity
  cold_le := le_rfl
  width := Or.inr rfl
  tail_gap := by norm_num [halfDegree,preE7CharacterRho]
  summed := by
    intro b P
    have hphysical :
        (∑ J : Subgroup (Equiv.Perm (Fin b)), fusionCompleteSourceSum (preE7NonPairAction 16 U) P J)≤
        ∑ J : Subgroup (Equiv.Perm (Fin b)), completeQuotientWeight (R := preE7NonPairAction 16 U) J := by
      apply Finset.sum_le_sum
      intro J _
      unfold fusionCompleteSourceSum completeQuotientWeight completeQuotientCount
      rw [Nat.cast_sum]
      exact Finset.sum_le_sum (fun N _ =>
        fusionSurvivingEpiCount_le_groupEpimorphism_card (preE7NonPairAction 16 U) P N J)
    exact hphysical.trans (complete_sum_le hU cover hZmud lit b)

end SymmetricSubgroupAsymptotics.OriginalNormalAxisSourceMenu
