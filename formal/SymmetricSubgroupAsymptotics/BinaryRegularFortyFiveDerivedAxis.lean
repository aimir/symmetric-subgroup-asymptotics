import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenJointSplitModels
import SymmetricSubgroupAsymptotics.BinaryPairKernelCard

/-! Rank saturation identifies the original derived subgroup with the
literal four-dimensional R45 axis. No split model is assumed for K45. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) [MulAction.IsPretransitive U X]

theorem regular45_original_card
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : F.kernelSpace = BinaryRegularEightSquareCarry.K45) : Nat.card U = 1024 := by
  have hk : F.kernelSpace = BinaryRegularEightNaturalRegistry.chart45.space :=
    hK.trans BinaryRegularEightNaturalRegistry.kernel45_space.symm
  have hc := F.kernelSpace_card_mul_top
  rw [hk, BinaryRegularEightNaturalRegistry.chart45.card,
    Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv, BinaryMenuCayley8T3.exact_card] at hc
  exact hc.symm

theorem regular45_derived_axis
    (hU : IsPGroup 2 U) (hrank : 6 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : F.kernelSpace = BinaryRegularEightSquareCarry.K45)
    (hR : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryRegularEightSquareCarry.R45) :
    commutator U = F.coordinateSubgroup BinaryRegularEightSquareCarry.R45 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hablo : 64 ≤ Nat.card (Abelianization U) := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hrank
    exact hp.trans (pGroup_pow_genRank_le_abelianization_card 2 hU)
  have hdegree : Nat.card X = 16 := by
    rw [← Nat.card_congr F.frame, Nat.card_prod, Nat.card_fin, Nat.card_zmod]
  have habhi := twoGroup_transitive_abelianization_card_le_quarter_add_two U hU
  rw [hdegree] at habhi
  have hab : Nat.card (Abelianization U) = 64 := by norm_num at habhi; omega
  have ht : Nat.card (Abelianization F.top.range) = 8 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).abelianizationCongr.toEquiv).trans
      BinaryEightTopAbelianizationCards.regular_abelianization_card
  have hmax := F.regular_axis_normalGen_le hU F.top.ker le_rfl hH
  have hgen : MarkedC4.normalGen F.top.ker = 3 := by
    have hext := F.abelianization_card_le_actual_kernel_normalGen hU
    rw [hab, ht] at hext
    have hp : 2 ^ 3 ≤ 2 ^ MarkedC4.normalGen F.top.ker := by nlinarith
    have hlo := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp
    omega
  have hsat := F.saturated_pair_kernel_radical hU (by rw [hab, hgen, ht]; norm_num)
  have he : F.coordinateSubgroup BinaryRegularEightSquareCarry.R45 =
      F.top.ker ⊓ commutator U := by
    rw [← hR, F.coordinateSubgroup_ambientAxis, hsat]
    exact inf_eq_right.mpr inf_le_left
  have hRle : BinaryRegularEightSquareCarry.R45 ≤ F.kernelSpace := by
    rw [← hR]
    exact F.ambientAxis_le_kernelSpace _
  have hRcard : Nat.card (F.coordinateSubgroup BinaryRegularEightSquareCarry.R45) = 16 := by
    rw [F.coordinateSubgroup_card _ hRle,
      ← BinaryRegularEightNaturalRegistry.radical45_space]
    exact (BinaryRegularEightNaturalRegistry.radicalCharts 45).2.card
  have hd : Nat.card (commutator U) ≤ 16 := by
    have hc := (commutator U).card_eq_card_quotient_mul_card_subgroup
    change Nat.card U = Nat.card (Abelianization U) * Nat.card (commutator U) at hc
    rw [F.regular45_original_card hH hK, hab] at hc
    omega
  have hle : F.coordinateSubgroup BinaryRegularEightSquareCarry.R45 ≤ commutator U := by
    rw [he]
    exact inf_le_right
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hRcard]; exact hd)).symm

end SymmetricSubgroupAsymptotics.BinaryPairFrame
