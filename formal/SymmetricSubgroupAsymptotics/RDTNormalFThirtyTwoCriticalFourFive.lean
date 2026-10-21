import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoRankFiveTopOrderExhaustion
import SymmetricSubgroupAsymptotics.BinaryPairRankNineCoarseNormalF
import SymmetricSubgroupAsymptotics.RDTNormalFThirtyTwoCriticalReduction

/-! The actual head-four/top-rank-five critical clause, on every SAME
original normal quotient. Derived and top-order budgets are proved from
the original pair geometry; no additional classification input remains. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem binary_thirty_two_critical_head_four_top_five_normalF_proved :
    BinaryThirtyTwoCriticalHeadTopNormalF 4 5 := by
  intro G hG _ F hrank hhead htop N _ _hN hnonab
  letI criticalFourFive_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := F.rank_nine_rank_five_top_derived_card_le_1024 hG hrank htop hhead.ge
  have hT := F.rank_five_top_card_le_1024_of_wide_original_kernel hG htop hhead.ge
  have hnon : ¬ ∀ t : F.top.range, t ^ 2 = 1 := by
    intro hpow
    letI criticalFourFive_topTransitive : MulAction.IsPretransitive F.top.range (Fin 16) :=
      F.top_pretransitive
    have hel : BinarySquareActionStructure.SquaresActTrivially
        (G := F.top.range) (X := Fin 16) :=
      BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mpr hpow
    have hb := ElementaryBinaryTransitiveNormalRank.normalGen_le_exponent
      hel (0 : Fin 16) 4 (by norm_num only [Nat.card_fin]) (⊤ : Subgroup F.top.range)
    letI criticalFourFive_topNilpotent : Group.IsNilpotent F.top.range :=
      (F.top_isPGroup hG).isNilpotent
    have hg := MarkedC4.genRank_le_normalGen_top (G := F.top.range)
    omega
  exact F.rank_nine_order_budget_top_1024_all_normal_unit hG hrank hD hT hnon N hnonab

end SymmetricSubgroupAsymptotics
