import SymmetricSubgroupAsymptotics.BinaryPairRankSixTopIntegralNormals
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoExcessOneAbelianization
import SymmetricSubgroupAsymptotics.PGroupElementaryAbelianizationRank
import SymmetricSubgroupAsymptotics.QuotientCenterIntegralCoinvariants

/-! Original rank-nine degree32 sources with actual rank-six top have
FULL integral proper-normal orders at most256. The normal preimage of an
arbitrary nonabelian quotient centre is retained exactly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance rankNineRankSixIntegralFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))

theorem rank_nine_rank_six_top_proper_normal_integral_order_le_256
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U=9)
    (hTopRank : 6≤MarkedC4.genRank F.top.range)
    (N : Subgroup U) [N.Normal] (hproper : N≠⊤) :
    normalIntegralCoinvariantOrder N≤256 := by
  have hdegree : Nat.card X=32 := by simpa only [Nat.card_fin] using F.card_points
  have hexp := binary_degree_thirty_two_rank_nine_abelianization_exponent U hU hdegree hrank
  have hAb : Nat.card (Abelianization U)=512 := by
    rw [pGroup_abelianization_card_eq_pow_genRank 2 hU hexp,hrank]
    decide
  by_cases hi : N.index=2
  · letI : IsCyclic (U ⧸ N) := isCyclic_of_prime_card (p := 2) (by exact hi)
    have hh := relative_integral_order_mul_index_of_cyclic_quotient N
    change normalIntegralCoinvariantOrder N*N.index=Nat.card (Abelianization U) at hh
    rw [hi,hAb] at hh
    omega
  · exact F.rank_six_top_large_index_normal_integral_order_le_two_fifty_six hU hTopRank (by omega) N
      (by have hh := N.one_lt_index_of_ne_top hproper;omega)

theorem rank_nine_rank_six_top_quotient_center_card_le_256
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U=9)
    (hTopRank : 6≤MarkedC4.genRank F.top.range)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬∀ a b : U ⧸ N,a*b=b*a) :
    Nat.card (Subgroup.center (U ⧸ N))≤256 := by
  apply quotient_center_card_le_of_large_index_integral_bound 256 ?_ N hnonab
  intro E hE hindex
  letI := hE
  apply F.rank_nine_rank_six_top_proper_normal_integral_order_le_256 hU hrank hTopRank E
  intro he
  have hh : E.index=1 := Subgroup.index_eq_one.mpr he
  omega
end SymmetricSubgroupAsymptotics.BinaryPairFrame
