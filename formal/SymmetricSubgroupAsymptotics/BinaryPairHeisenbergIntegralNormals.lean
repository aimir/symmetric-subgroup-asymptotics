import SymmetricSubgroupAsymptotics.BinaryPairLiteralMixedIntegralTransfer
import SymmetricSubgroupAsymptotics.BinaryPairIndexDimensionBudget
import SymmetricSubgroupAsymptotics.BinaryPairNormalIntersectionRadicalCut
import SymmetricSubgroupAsymptotics.BinaryHeisenbergTopIntegralBounds
import SymmetricSubgroupAsymptotics.BinaryHeisenbergIntegralMixedCapacities
import SymmetricSubgroupAsymptotics.BinaryPairDegreeEightAxisBounds
import SymmetricSubgroupAsymptotics.PGroupElementaryAbelianizationRank
import SymmetricSubgroupAsymptotics.RelativeIntegralCyclicQuotient
import SymmetricSubgroupAsymptotics.RelativeIntegralIndexFour

/-! Every proper original normal in the actual Heisenberg pair-top source
has integral relative quotient of order at most sixteen. Both surviving
boundary tests concern the original kernel and original normal radical. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

theorem heisenberg_pair_top_proper_normal_integral_order_le_sixteen
    (hU : IsPGroup 2 U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hAb : Nat.card (Abelianization U) ≤ 32)
    (E : Subgroup U) [E.Normal] (hproper : E ≠ ⊤) :
    normalIntegralCoinvariantOrder E ≤ 16 := by
  letI heisenbergIntegralNormals_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f := F.top.rangeRestrict
  let A := E ⊓ F.top.ker
  let L := primeRelativeRadical 2 A
  have hA : A ≤ F.top.ker := inf_le_right
  have htop : Nat.card F.top.range = 32 := by
    rw [hH]
    exact BinaryMenuCayley8T22.exact_card
  by_cases htwo : E.index = 2
  · letI heisenbergIntegralNormals_cyclic : IsCyclic (U ⧸ E) := isCyclic_of_prime_card htwo
    exact relative_integral_order_le_sixteen_of_cyclic_quotient E hAb (by omega)
  by_cases hfour : E.index = 4
  · exact normalIntegralCoinvariantOrder_le_sixteen_of_index_four E hfour hAb
  have hindex : 8 ≤ E.index := by
    obtain ⟨k, hk⟩ := (hU.to_quotient E).exists_card_eq
    change E.index = 2 ^ k at hk
    have hproperIndex := E.one_lt_index_of_ne_top hproper
    have hk3 : 3 ≤ k := by
      by_contra hn
      have hkcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hkcases with rfl | rfl | rfl
      · change E.index = 1 at hk
        omega
      · change E.index = 2 at hk
        exact htwo hk
      · change E.index = 4 at hk
        exact hfour hk
    rw [hk]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hk3
  by_cases hfull : E.map f = ⊤
  · letI heisenbergIntegralNormals_kernelComm : IsMulCommutative F.top.ker := ⟨⟨fun a b =>
      F.bitsHom_injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
    have hsup : E ⊔ F.top.ker = ⊤ := by
      have h := congrArg (Subgroup.comap f) hfull
      simpa only [Subgroup.comap_map_eq, Subgroup.comap_top, f,
        MonoidHom.ker_rangeRestrict] using h
    have he := relative_integral_order_mul_index_of_abelian_supplement E F.top.ker hsup
    change (⁅E, (⊤ : Subgroup U)⁆).relIndex E ≤ 16
    nlinarith
  letI heisenbergIntegralNormals_imageNormal : (E.map f).Normal :=
    Subgroup.Normal.map inferInstance f F.top.rangeRestrict_surjective
  have hcenter : Nat.card (Subgroup.center F.top.range) ≤ 2 := by
    have hc := Nat.card_congr (Subgroup.centerCongr (MulEquiv.subgroupCongr hH)).toEquiv
    exact hc.le.trans BinaryHeisenbergTopIntegralBounds.center_card_le_two
  have hT : Nat.card (E.map f) ≤ 16 := by
    have hi := (E.map f).one_lt_index_of_ne_top hfull
    have hc := (E.map f).card_mul_index
    rw [htop] at hc
    nlinarith
  have hTint : normalIntegralCoinvariantOrder (E.map f) ≤ 8 :=
    normalIntegralCoinvariantOrder_le_of_card_center (E.map f) 8 hT
      (hcenter.trans (by decide))
  have hlift := normalIntegralCoinvariantOrder_le_elementary_kernel 2 hU f
    F.top.rangeRestrict_surjective (by
      intro k
      exact F.physical_kernel_pow_two ⟨k.val, by simpa only [f, MonoidHom.ker_rangeRestrict] using k.property⟩) E
  dsimp only [f] at hlift
  rw [MonoidHom.ker_rangeRestrict] at hlift
  change normalIntegralCoinvariantOrder E ≤
    2 ^ MarkedC4.normalGen A * normalIntegralCoinvariantOrder (E.map f) at hlift
  have hhead := F.heisenberg_axis_normalGen_le hU A hA hH
  by_cases hsmall : MarkedC4.normalGen A ≤ 1
  · have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hsmall
    have hb := hlift.trans (Nat.mul_le_mul hp hTint)
    norm_num at hb
    exact hb
  by_cases hTsmall : Nat.card (E.map f) ≤ 8
  · have hsmallInt := normalIntegralCoinvariantOrder_le_of_card_center (E.map f) 4 hTsmall
      (hcenter.trans (by decide))
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hhead
    have hb := hlift.trans (Nat.mul_le_mul hp hsmallInt)
    norm_num at hb
    exact hb
  have hT16 : Nat.card (E.map f) = 16 := by
    obtain ⟨k, hk⟩ := ((F.top_isPGroup hU).to_subgroup (E.map f)).exists_card_eq
    have hk4 : 4 ≤ k := by
      by_contra hn
      have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show k ≤ 3 by omega)
      change 2 ^ k ≤ 8 at hp
      rw [← hk] at hp
      exact hTsmall hp
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hk4
    change 16 ≤ 2 ^ k at hp
    rw [← hk] at hp
    omega
  have hdim := F.intersection_finrank_add_two_le_kernel_of_index_ge_eight E htop hT16 hindex
  have hKdim : Module.finrank (ZMod 2) F.kernelSpace ≤ 8 := by
    simpa using Submodule.finrank_le F.kernelSpace
  have hcut : L ≤ ⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker :=
    F.intersection_relativeRadical_le_actual_commutator E
  have hprice : Nat.card A ≤ 4 * Nat.card L := by
    have he := primeRelativeRadical_card_factorization 2 A
    rw [← pGroup_normalGen_eq_primeRelativeHead 2 hU A] at he
    exact he.le.trans (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hhead))
  let W := F.literalTopKernel BinaryHeisenbergEightNaturalHeads.H hH
  have hW : W.toSubmodule = F.kernelSpace :=
    F.literalTopKernel_space BinaryHeisenbergEightNaturalHeads.H hH
  rcases F.heisenberg_large_axis_models hU A hA hH (by omega) with h12 | h13 | h14
  · have hd : Module.finrank (ZMod 2) (F.ambientAxis A) = 7 := by
      rw [h12.1, ← BinaryHeisenbergEightNaturalHeads.kernel12_space,
        BinaryHeisenbergEightNaturalHeads.states_space]
      exact (BinaryHeisenbergEightNaturalHeads.charts 12).2.finrank
    rw [hd] at hdim
    omega
  · have hd : Module.finrank (ZMod 2) (F.ambientAxis A) = 5 := by
      rw [h13.1, ← BinaryHeisenbergEightNaturalHeads.kernel13_space,
        BinaryHeisenbergEightNaturalHeads.states_space]
      exact (BinaryHeisenbergEightNaturalHeads.charts 13).2.finrank
    have htest : BinaryHeisenbergEightSquareCarry.K12 ≤ F.kernelSpace := by
      rw [← hW]
      apply BinaryHeisenbergIntegralMixedCapacities.kernel_contains12_of_finrank_ge_seven W
      rw [hW]
      rw [hd] at hdim
      omega
    have hb := F.integral_order_le_two_mul_top_of_literal_mixed_capacity
      BinaryHeisenbergEightNaturalHeads.H hH
      BinaryHeisenbergEightSquareCarry.K12 BinaryHeisenbergEightSquareCarry.R13 htest
      E L h13.2 hcut 8
      BinaryHeisenbergIntegralMixedPilot.top_kernel_augmentation_radical13_le_eight
      (by rw [hT16]; decide) hprice
    change normalIntegralCoinvariantOrder E ≤
      2 * normalIntegralCoinvariantOrder (E.map f) at hb
    exact hb.trans (Nat.mul_le_mul_left 2 hTint)
  · have hd : Module.finrank (ZMod 2) (F.ambientAxis A) = 3 := by
      rw [h14.1, ← BinaryHeisenbergEightNaturalHeads.kernel14_space,
        BinaryHeisenbergEightNaturalHeads.states_space]
      exact (BinaryHeisenbergEightNaturalHeads.charts 14).2.finrank
    have htest : BinaryHeisenbergEightSquareCarry.K13 ≤ F.kernelSpace := by
      rw [← hW]
      apply BinaryHeisenbergIntegralMixedCapacities.kernel_contains13_of_finrank_ge_five W
      rw [hW]
      rw [hd] at hdim
      omega
    have hb := F.integral_order_le_two_mul_top_of_literal_mixed_capacity
      BinaryHeisenbergEightNaturalHeads.H hH
      BinaryHeisenbergEightSquareCarry.K13 BinaryHeisenbergEightSquareCarry.R14 htest
      E L h14.2 hcut 8
      BinaryHeisenbergIntegralMixedCapacities.top_kernel_axis13_radical14_le_eight
      (by rw [hT16]; decide) hprice
    change normalIntegralCoinvariantOrder E ≤
      2 * normalIntegralCoinvariantOrder (E.map f) at hb
    exact hb.trans (Nat.mul_le_mul_left 2 hTint)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
