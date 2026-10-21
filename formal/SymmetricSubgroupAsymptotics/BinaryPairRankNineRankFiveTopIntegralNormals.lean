import SymmetricSubgroupAsymptotics.BinaryPairRankFiveTopIntegralNormals
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoExcessOneAbelianization
import SymmetricSubgroupAsymptotics.PGroupElementaryAbelianizationRank
import SymmetricSubgroupAsymptotics.QuotientCenterIntegralCoinvariants

/-! Original rank-nine degree32 sources with actual rank-five top have
full integral proper-normal orders at most256, hence the same bound on
the center of every nonabelian original normal quotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))

theorem rank_nine_rank_five_top_proper_normal_integral_order_le_256
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U = 9)
    (hTopRank : MarkedC4.genRank F.top.range = 5)
    (E : Subgroup U) [E.Normal] (hproper : E ≠ ⊤) :
    normalIntegralCoinvariantOrder E ≤ 256 := by
  letI rankNineFiveTopIntegral_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdegree : Nat.card X = 32 := by rw [F.card_points]; simp only [Nat.card_fin]
  have hexp := binary_degree_thirty_two_rank_nine_abelianization_exponent U hU hdegree hrank
  have hAb : Nat.card (Abelianization U) = 512 := by
    rw [pGroup_abelianization_card_eq_pow_genRank 2 hU hexp, hrank]
    decide
  exact F.rank_five_top_proper_normal_integral_order_le_256 hU hTopRank hAb.le E hproper

/-- The normal preimage of the SAME quotient center has index at least
four, so its full integral quotient bounds the actual center. -/
theorem rank_nine_rank_five_top_quotient_center_card_le_256
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U = 9)
    (hTopRank : MarkedC4.genRank F.top.range = 5)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    Nat.card (Subgroup.center (U ⧸ N)) ≤ 256 := by
  apply quotient_center_card_le_of_large_index_integral_bound 256 ?_ N hnonab
  intro E hE hindex
  letI rankNineFiveTopCenter_normal : E.Normal := hE
  apply F.rank_nine_rank_five_top_proper_normal_integral_order_le_256 hU hrank hTopRank E
  intro htop
  rw [htop, Subgroup.index_top] at hindex
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
