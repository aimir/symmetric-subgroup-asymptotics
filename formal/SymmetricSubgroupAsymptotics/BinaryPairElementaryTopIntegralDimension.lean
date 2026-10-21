import SymmetricSubgroupAsymptotics.BinaryPairElementaryHeadSixDimension
import SymmetricSubgroupAsymptotics.BinaryPairHalfTopIndexDimensionGeneral
import SymmetricSubgroupAsymptotics.NormalIntegralCoinvariantExtension
import SymmetricSubgroupAsymptotics.RelativeIntegralAbelianSupplement
import SymmetricSubgroupAsymptotics.BinaryPairLiftCarryExponent

/-! Full integral relative coinvariants for an elementary sixteen-point
top. The same original normal and its kernel intersection supply both
the lift and the exact index/dimension contradiction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))

theorem elementary_top_integral_order_le_256_of_dimension_index
    (hU : IsPGroup 2 U) (hpow : ∀ t : F.top.range, t ^ 2 = 1)
    (d : ℕ) (hd : 1 ≤ d)
    (hK : Module.finrank (ZMod 2) F.kernelSpace ≤ 10 + d)
    (hAb : Nat.card (Abelianization U) ≤ 1024)
    (N : Subgroup U) [N.Normal] (hindex : 2 ^ (d + 1) ≤ N.index) :
    normalIntegralCoinvariantOrder N ≤ 256 := by
  letI elementaryTopIntegral_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI elementaryTopIntegral_topTransitive : MulAction.IsPretransitive F.top.range (Fin 16) :=
    F.top_pretransitive
  have hTop := F.top_isPGroup hU
  have hel : BinarySquareActionStructure.SquaresActTrivially
      (G := F.top.range) (X := Fin 16) :=
    BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mpr hpow
  have hTopCard : Nat.card F.top.range = 16 := by
    simpa only [Nat.card_fin] using ElementaryBinaryTransitiveNormalRank.card_eq_degree
      hel (0 : Fin 16)
  let f := F.top.rangeRestrict
  have hf : Function.Surjective f := F.top.rangeRestrict_surjective
  by_cases hfull : N.map f = ⊤
  · letI elementaryTopIntegral_kernelComm : IsMulCommutative F.top.ker := ⟨⟨fun a b =>
      F.bitsHom_injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
    have hsup : N ⊔ F.top.ker = ⊤ := by
      have hh := congrArg (Subgroup.comap f) hfull
      simpa only [Subgroup.comap_map_eq, Subgroup.comap_top, f,
        MonoidHom.ker_rangeRestrict] using hh
    have he := relative_integral_order_mul_index_of_abelian_supplement N F.top.ker hsup
    change normalIntegralCoinvariantOrder N * N.index = Nat.card (Abelianization U) at he
    have hi : 4 ≤ N.index := (show 2 ^ 2 ≤ 2 ^ (d + 1) from
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega)).trans hindex
    have hm : normalIntegralCoinvariantOrder N * 4 ≤ 1024 :=
      (Nat.mul_le_mul_left _ hi).trans (he.le.trans hAb)
    omega
  letI elementaryTopIntegral_imageNormal : (N.map f).Normal :=
    Subgroup.Normal.map inferInstance f hf
  have hTcard : Nat.card (N.map f) ≤ 8 := by
    have hi := (N.map f).one_lt_index_of_ne_top hfull
    have hc := (N.map f).card_mul_index
    rw [hTopCard] at hc
    nlinarith [Nat.card_pos (α := N.map f)]
  have hTint : normalIntegralCoinvariantOrder (N.map f) ≤ Nat.card (N.map f) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card _ _)
  have hpowers : ∀ k : f.ker, (k : U) ^ 2 = 1 := by
    intro k
    exact F.physical_kernel_pow_two
      ⟨k.val, by simpa only [f, MonoidHom.ker_rangeRestrict] using k.property⟩
  have hb : normalIntegralCoinvariantOrder N ≤
      2 ^ MarkedC4.normalGen (N ⊓ F.top.ker) * normalIntegralCoinvariantOrder (N.map f) := by
    simpa only [f, MonoidHom.ker_rangeRestrict] using
      normalIntegralCoinvariantOrder_le_elementary_kernel 2 hU f hf hpowers N
  have hhead : MarkedC4.normalGen (N ⊓ F.top.ker) ≤ 6 := by
    let W := F.axisNaturalSubrepresentation (N ⊓ F.top.ker)
    have hh := twoGroup_permutationSubrepresentationHead_le_width hTop 4
      (by norm_num only [Nat.card_fin]) (0 : Fin 16) W
    rw [representationHead_finrank_eq_coinvariants,
      ← F.axisNatural_normalGen (N ⊓ F.top.ker) inf_le_right hU] at hh
    norm_num [Nat.choose] at hh
    exact hh
  by_cases hsmall : MarkedC4.normalGen (N ⊓ F.top.ker) ≤ 5
  · exact hb.trans ((Nat.mul_le_mul
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hsmall)
      (hTint.trans hTcard)).trans (by decide))
  by_cases hTsmall : Nat.card (N.map f) ≤ 4
  · exact hb.trans ((Nat.mul_le_mul
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hhead)
      (hTint.trans hTsmall)).trans (by decide))
  have hTeight : Nat.card (N.map f) = 8 := by
    obtain ⟨j, hj⟩ := (hTop.to_subgroup (N.map f)).exists_card_eq
    have hhi : j ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      (by simpa only [← hj] using hTcard)
    have hlo : 3 ≤ j := by
      by_contra hn
      have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show j ≤ 2 by omega)
      have hc : Nat.card (N.map f) ≤ 4 := by simpa only [← hj] using hp
      exact hTsmall hc
    rw [hj, show j = 3 by omega]
    norm_num
  have hhalf : Nat.card F.top.range = 2 * Nat.card (N.map F.top.rangeRestrict) := by
    change Nat.card F.top.range = 2 * Nat.card (N.map f)
    rw [hTopCard, hTeight]
  have hgap := F.intersection_finrank_add_le_kernel_of_half_top_index N d hhalf hindex
  have hdim := F.elementary_top_axis_finrank_ge_eleven_of_normalGen_six hU hpow
    (N ⊓ F.top.ker) inf_le_right (by omega)
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
