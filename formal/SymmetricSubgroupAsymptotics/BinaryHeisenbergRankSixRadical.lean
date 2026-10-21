import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenJointSplitModels

/-! Full rank-six abelianization saturation retains the literal original
Heisenberg pair-kernel radical for every one of its three large kernels. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) [MulAction.IsPretransitive U X]

theorem heisenberg_rank_six_kernel_radical_eq
    (hU : IsPGroup 2 U) (hrank : 6 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators)) :
    primeRelativeRadical 2 F.top.ker = F.top.ker ⊓ commutator U := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdegree : Nat.card X = 16 := by
    rw [← Nat.card_congr F.frame, Nat.card_prod, Nat.card_fin, Nat.card_zmod]
  have habhi := twoGroup_transitive_abelianization_card_le_quarter_add_two U hU
  rw [hdegree] at habhi
  have hablo : 64 ≤ Nat.card (Abelianization U) :=
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hrank).trans
      (pGroup_pow_genRank_le_abelianization_card 2 hU)
  have hab : Nat.card (Abelianization U) = 64 := by norm_num at habhi; omega
  have ht : Nat.card (Abelianization F.top.range) = 16 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).abelianizationCongr.toEquiv).trans
      BinaryEightTopAbelianizationCards.heisenberg_abelianization_card
  have hmax := F.heisenberg_axis_normalGen_le hU F.top.ker le_rfl hH
  have hgen : MarkedC4.normalGen F.top.ker = 2 := by
    have hext := F.abelianization_card_le_actual_kernel_normalGen hU
    rw [hab, ht] at hext
    have hp : 2 ^ 2 ≤ 2 ^ MarkedC4.normalGen F.top.ker := by nlinarith
    have hlo := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp
    omega
  apply F.saturated_pair_kernel_radical hU
  rw [hab, hgen, ht]
  norm_num

end SymmetricSubgroupAsymptotics.BinaryPairFrame
