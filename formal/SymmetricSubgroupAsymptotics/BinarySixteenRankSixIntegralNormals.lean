import SymmetricSubgroupAsymptotics.NormalIntegralCoinvariantQuotientCenterBound
import SymmetricSubgroupAsymptotics.RDTNormalFSixteenRankSix
import SymmetricSubgroupAsymptotics.BinaryTransitiveAbelianizationQuarterPlusTwo

/-! The independently proved sixteen-point excess-two normal-F packet
bounds all nonabelian quotient centres. This controls FULL integral
coinvariants of normal subgroups of index at least four. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open MarkedC4.ActualNormalFMarkedPeel MarkedC4.RDTNormalFInterface
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (E : BinaryPairFrame U (Fin 8)) [MulAction.IsPretransitive U X]
include E

theorem sixteen_rank_six_nonabelian_quotient_center_le_sixteen
    (hU : IsPGroup 2 U) (hrank : 6≤MarkedC4.genRank U)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬∀ x y : U ⧸ N,x*y=y*x) :
    Nat.card (Subgroup.center (U ⧸ N))≤16 := by
  obtain ⟨V,_,_,hz⟩ := E.sixteen_rank_six_all_normal_quotients hU hrank N hnonab
  have hc : Nat.card (targetCentralizer V)≤16 := by
    change Real.logb 2 (Nat.card (targetCentralizer V) : ℝ)≤4 at hz
    have hp : (0 : ℝ)<Nat.card (targetCentralizer V) := by exact_mod_cast Nat.card_pos
    have hr := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2) hp).mp hz
    norm_num at hr
    exact_mod_cast hr
  exact (Subgroup.card_le_of_le (Subgroup.center_le_centralizer (V : Set (U ⧸ N)))).trans hc

theorem sixteen_rank_six_large_index_normal_integral_order_le_sixteen
    (hU : IsPGroup 2 U) (hrank : 6≤MarkedC4.genRank U)
    (N : Subgroup U) [N.Normal] (hindex : 4≤N.index) :
    normalIntegralCoinvariantOrder N≤16 := by
  have hdegree : Nat.card X=16 := by simpa only [Nat.card_fin] using E.card_points
  have hAb : Nat.card (Abelianization U)≤64 := by
    have hh := twoGroup_transitive_abelianization_card_le_quarter_add_two U hU
    rw [hdegree] at hh
    norm_num at hh
    exact hh
  apply normalIntegralCoinvariantOrder_le_of_quotient_center_bound N 16
  · omega
  · intro C _ hnon
    exact E.sixteen_rank_six_nonabelian_quotient_center_le_sixteen hU hrank C hnon
end SymmetricSubgroupAsymptotics.BinaryPairFrame
