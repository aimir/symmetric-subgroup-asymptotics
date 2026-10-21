import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoElementaryKernelDimension
import SymmetricSubgroupAsymptotics.BinaryPairRankNineElementaryIntegralNormals
import SymmetricSubgroupAsymptotics.BinaryPairRankNineRankFiveTopIntegralNormals
import SymmetricSubgroupAsymptotics.BinaryPairRankNineRankSixTopIntegralNormals

/-! Every nonabelian quotient of the SAME original rank-nine degree32
source has center order at most256. Elementary and nonelementary actual
tops are dispatched internally; no extra structural case is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))

include F

theorem rank_nine_nonabelian_quotient_center_card_le_256
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U = 9)
    (N : Subgroup U) [N.Normal] (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    Nat.card (Subgroup.center (U ⧸ N)) ≤ 256 := by
  by_cases hpow : ∀ t : F.top.range, t ^ 2 = 1
  · exact F.rank_nine_elementary_quotient_center_card_le_256_of_kernel_dimension
      hU hrank hpow (F.rank_nine_elementary_kernel_finrank_le_twelve hU hrank.ge hpow) N hnonab
  · letI rankNineQuotientCenters_topTransitive : MulAction.IsPretransitive F.top.range (Fin 16) :=
      F.top_pretransitive
    have hTop := F.top_isPGroup hU
    have hk : MarkedC4.normalGen F.top.ker ≤ 4 := by
      let W := F.axisNaturalSubrepresentation F.top.ker
      have hh := twoGroup_faithful_permutationSubrepresentationHead_le_quarter hTop hpow W
      rw [representationHead_finrank_eq_coinvariants,
        ← F.axisNatural_normalGen F.top.ker le_rfl hU] at hh
      norm_num only [Nat.card_fin] at hh
      exact hh
    have hg : MarkedC4.genRank U ≤
        MarkedC4.normalGen F.top.ker + MarkedC4.genRank F.top.range := by
      letI rankNineQuotientCenters_kernelComm : IsMulCommutative F.top.ker := ⟨⟨fun a b =>
        F.bitsHom_injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
      letI rankNineQuotientCenters_rangeKernelComm : IsMulCommutative F.top.rangeRestrict.ker := by
        rw [MonoidHom.ker_rangeRestrict]
        infer_instance
      have hh := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
        F.top.rangeRestrict F.top.rangeRestrict_surjective
      rw [MonoidHom.ker_rangeRestrict] at hh
      omega
    by_cases hfive : MarkedC4.genRank F.top.range = 5
    · exact F.rank_nine_rank_five_top_quotient_center_card_le_256 hU hrank hfive N hnonab
    · have hsix : 6 ≤ MarkedC4.genRank F.top.range := by omega
      exact F.rank_nine_rank_six_top_quotient_center_card_le_256 hU hrank hsix N hnonab

end BinaryPairFrame

/-- This export quantifies directly over the original action and its
original quotient denominator, with no displayed pair frame required. -/
theorem binary_degree_thirty_two_rank_nine_quotient_center_card_le_256
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 32) (hrank : MarkedC4.genRank U = 9)
    (N : Subgroup U) [N.Normal] (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    Nat.card (Subgroup.center (U ⧸ N)) ≤ 256 := by
  obtain ⟨F⟩ := transitiveBinaryPairFrame_nonempty 4 U hU (by
    norm_num only [Nat.reduceAdd, Nat.reducePow]
    exact hdegree)
  exact F.rank_nine_nonabelian_quotient_center_card_le_256 hU hrank N hnonab

end SymmetricSubgroupAsymptotics
