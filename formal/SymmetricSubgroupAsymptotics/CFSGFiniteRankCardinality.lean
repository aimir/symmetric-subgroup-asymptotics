import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailSource
import Mathlib.GroupTheory.Rank
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Ordinary finite-group rank is bounded by the base-two logarithm
of the actual order. No normal-generation or permutation-rank input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteRankCardinality
variable (G : Type*) [Group G] [Finite G]

theorem rank_le_logb_card : (Group.rank G : ℝ) ≤ Real.logb 2 (Nat.card G) := by
  obtain ⟨S, hS, hp⟩ := exists_generating_finset_two_pow_le G
  have hpow : (2 : ℝ) ^ S.card ≤ Nat.card G := by exact_mod_cast hp
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow
  have hs : (S.card : ℝ) ≤ Real.logb 2 (Nat.card G) := by
    simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using hlog
  have hr : (Group.rank G : ℝ) ≤ S.card := by exact_mod_cast Group.rank_le hS
  exact hr.trans hs

theorem subgroup_rank_le_logb_card (H : Subgroup G) :
    (Group.rank H : ℝ) ≤ Real.logb 2 (Nat.card G) := by
  refine (rank_le_logb_card H).trans ?_
  apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
  · exact_mod_cast (Nat.card_pos (α := H))
  · exact_mod_cast Subgroup.card_le_card_group H

end SymmetricSubgroupAsymptotics.CFSGFiniteRankCardinality
