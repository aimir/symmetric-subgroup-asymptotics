import SymmetricSubgroupAsymptotics.BinaryPairRegularExceptionalIntegral
import SymmetricSubgroupAsymptotics.BinaryPairDegreeEightAxisBounds
import SymmetricSubgroupAsymptotics.BinaryPairSmallTopLargeKernel
import SymmetricSubgroupAsymptotics.RelativeIntegralCyclicQuotient
import SymmetricSubgroupAsymptotics.RelativeIntegralIndexFour

/-! Full integral relative orders for every proper original normal of
a rank-five eight-pair group with literal regular elementary top. The
exceptional natural axis uses an actual mixed bit, not its mod-two rank. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))
    [MulAction.IsPretransitive F.top.range (Fin 8)]

theorem regular_pair_top_proper_normal_integral_order_le_sixteen
    (hU : IsPGroup 2 U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (htoprank : MarkedC4.genRank F.top.range ≤ 3)
    (hrank : MarkedC4.genRank U = 5)
    (hexp : ∀ a : Abelianization U, a ^ 2 = 1)
    (E : Subgroup U) [E.Normal] (hproper : E ≠ ⊤) :
    normalIntegralCoinvariantOrder E ≤ 16 := by
  letI regularIntegralNormals_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f := F.top.rangeRestrict
  let A := E ⊓ F.top.ker
  have hA : A ≤ F.top.ker := inf_le_right
  have htop : Nat.card F.top.range = 8 := by rw [hH]; exact BinaryMenuCayley8T3.exact_card
  have hAb : Nat.card (Abelianization U) = 32 := by
    rw [pGroup_abelianization_card_eq_pow_genRank 2 hU hexp, hrank]
    decide
  by_cases htwo : E.index = 2
  · letI regularIntegralNormals_cyclic : IsCyclic (U ⧸ E) := isCyclic_of_prime_card htwo
    exact relative_integral_order_le_sixteen_of_cyclic_quotient E hAb.le (by omega)
  by_cases hfour : E.index = 4
  · exact normalIntegralCoinvariantOrder_le_sixteen_of_index_four E hfour hAb.le
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
  · letI regularIntegralNormals_kernelComm : IsMulCommutative F.top.ker := ⟨⟨fun a b =>
      F.bitsHom_injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
    have hsup : E ⊔ F.top.ker = ⊤ := by
      have h := congrArg (Subgroup.comap f) hfull
      simpa only [Subgroup.comap_map_eq, Subgroup.comap_top, f,
        MonoidHom.ker_rangeRestrict] using h
    have he := relative_integral_order_mul_index_of_abelian_supplement E F.top.ker hsup
    rw [hAb] at he
    change (⁅E, (⊤ : Subgroup U)⁆).relIndex E ≤ 16
    nlinarith
  have hT : Nat.card (E.map f) ≤ 4 := by
    have hi := (E.map f).one_lt_index_of_ne_top hfull
    have hc := (E.map f).card_mul_index
    rw [htop] at hc
    nlinarith
  have hTint : normalIntegralCoinvariantOrder (E.map f) ≤ Nat.card (E.map f) :=
    Nat.le_of_dvd Nat.card_pos
      (Subgroup.relIndex_dvd_card (⁅E.map f, (⊤ : Subgroup F.top.range)⁆) (E.map f))
  have hlift := normalIntegralCoinvariantOrder_le_elementary_kernel 2 hU f
    F.top.rangeRestrict_surjective (by
      intro k
      exact F.physical_kernel_pow_two ⟨k.val, by simpa only [f, MonoidHom.ker_rangeRestrict] using k.property⟩) E
  dsimp only [f] at hlift
  rw [MonoidHom.ker_rangeRestrict] at hlift
  change normalIntegralCoinvariantOrder E ≤
    2 ^ MarkedC4.normalGen A * normalIntegralCoinvariantOrder (E.map f) at hlift
  have hhead := F.regular_axis_normalGen_le hU A hA hH
  by_cases hsmall : MarkedC4.normalGen A ≤ 2
  · have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hsmall
    have hb := hlift.trans (Nat.mul_le_mul hp (hTint.trans hT))
    norm_num at hb
    exact hb
  by_cases hTtwo : Nat.card (E.map f) ≤ 2
  · have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hhead
    have hb := hlift.trans (Nat.mul_le_mul hp (hTint.trans hTtwo))
    norm_num at hb
    exact hb
  have hTfour : Nat.card (E.map f) = 4 := by
    have hd := Subgroup.card_subgroup_dvd_card (E.map f)
    rw [htop] at hd
    have he : Nat.card (E.map f) = 3 ∨ Nat.card (E.map f) = 4 := by omega
    rcases he with h3 | h4
    · rw [h3] at hd
      norm_num at hd
    · exact h4
  rcases F.regular_large_axis_models hU A hA hH (by omega) with h45 | h46
  · have hdA : Module.finrank (ZMod 2) (F.ambientAxis A) = 7 := by
      rw [h45.1, ← BinaryRegularEightNaturalRegistry.kernel45_space,
        BinaryRegularEightNaturalRegistry.states_space]
      exact BinaryRegularEightNaturalRegistry.chart45.finrank
    have hAc : Nat.card A = 128 := by
      have hc := F.axis_card_eq_kernel_intersection A
      rw [inf_eq_right.mpr hA] at hc
      rw [← hc]
      simpa only [Nat.card_zmod, hdA] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.ambientAxis A))
    have hEc : Nat.card E = 512 := by
      have hc := subgroup_card_eq_map_mul_kernel_intersection f E
      dsimp only [f] at hc
      rw [MonoidHom.ker_rangeRestrict, hTfour] at hc
      change Nat.card E = 4 * Nat.card A at hc
      rw [hAc] at hc
      exact hc
    have hKdim := F.kernel_finrank_le_seven_of_rank_five hU (by omega) htoprank
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hKdim
    have hk : Nat.card F.kernelSpace = 2 ^ Module.finrank (ZMod 2) F.kernelSpace := by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.kernelSpace))
    have hc := F.kernelSpace_card_mul_top
    rw [htop, hk] at hc
    have hi := E.card_mul_index
    rw [hEc] at hi
    norm_num at hp
    omega
  · exact F.regular_exceptional_integral_order_le_sixteen_of_index_ge_eight hU E
      htop hTfour hindex h46.1 h46.2

end SymmetricSubgroupAsymptotics.BinaryPairFrame
