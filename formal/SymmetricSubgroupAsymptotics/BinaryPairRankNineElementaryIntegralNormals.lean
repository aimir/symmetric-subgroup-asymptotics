import SymmetricSubgroupAsymptotics.BinaryPairElementaryIntegralCenterConsumers
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoExcessOneAbelianization
import SymmetricSubgroupAsymptotics.PGroupElementaryAbelianizationRank

/-! The original rank-nine abelianization supplies the order512 budget
for the elementary-top integral consumer. The kernel dimension is kept
as an explicit checked geometric input, separate from its full integral
conclusion. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))

theorem rank_nine_elementary_large_index_integral_order_le_256_of_kernel_dimension
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U = 9)
    (hpow : ∀ t : F.top.range, t ^ 2 = 1)
    (hK : Module.finrank (ZMod 2) F.kernelSpace ≤ 12)
    (N : Subgroup U) [N.Normal] (hindex : 2 < N.index) :
    normalIntegralCoinvariantOrder N ≤ 256 := by
  letI rankNineElementaryIntegral_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdegree : Nat.card X = 32 := by rw [F.card_points]; simp only [Nat.card_fin]
  have hexp := binary_degree_thirty_two_rank_nine_abelianization_exponent U hU hdegree hrank
  have hAb : Nat.card (Abelianization U) = 512 := by
    rw [pGroup_abelianization_card_eq_pow_genRank 2 hU hexp, hrank]
    decide
  exact F.elementary_top_large_index_integral_order_le_256_of_kernel_dimension_twelve
    hU hpow hK hAb.le N hindex

theorem rank_nine_elementary_quotient_center_card_le_256_of_kernel_dimension
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U = 9)
    (hpow : ∀ t : F.top.range, t ^ 2 = 1)
    (hK : Module.finrank (ZMod 2) F.kernelSpace ≤ 12)
    (N : Subgroup U) [N.Normal] (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    Nat.card (Subgroup.center (U ⧸ N)) ≤ 256 := by
  apply quotient_center_card_le_of_large_index_integral_bound 256 ?_ N hnonab
  intro E hE hindex
  letI rankNineElementaryCenter_normal : E.Normal := hE
  exact F.rank_nine_elementary_large_index_integral_order_le_256_of_kernel_dimension
    hU hrank hpow hK E hindex

end SymmetricSubgroupAsymptotics.BinaryPairFrame
