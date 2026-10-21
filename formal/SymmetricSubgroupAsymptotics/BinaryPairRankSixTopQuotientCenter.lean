import SymmetricSubgroupAsymptotics.BinaryPairRankSixTopIntegralNormals
import SymmetricSubgroupAsymptotics.QuotientCenterIntegralCoinvariants

/-! The universal degree32 full-abelianization ceiling1024 suffices for
actual rank-six tops. Every nonabelian original normal quotient has centre
at most256, including excess-two sources; no rank-nine budget is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))

theorem rank_six_top_nonabelian_quotient_center_card_le_256
    (hU : IsPGroup 2 U) (hTopRank : 6≤MarkedC4.genRank F.top.range)
    (N : Subgroup U) [N.Normal] (hnonab : ¬∀ a b : U ⧸ N,a*b=b*a) :
    Nat.card (Subgroup.center (U ⧸ N))≤256 := by
  have hdegree : Nat.card X=32 := by simpa only [Nat.card_fin] using F.card_points
  have hAb : Nat.card (Abelianization U)≤1024 := by
    have hh := twoGroup_transitive_abelianization_card_le_quarter_add_two U hU
    rw [hdegree] at hh
    norm_num at hh
    exact hh
  apply quotient_center_card_le_of_large_index_integral_bound 256 ?_ N hnonab
  intro E hE hindex
  letI := hE
  exact F.rank_six_top_large_index_normal_integral_order_le_two_fifty_six hU hTopRank hAb E hindex
end SymmetricSubgroupAsymptotics.BinaryPairFrame
