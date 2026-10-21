import SymmetricSubgroupAsymptotics.NormalFUnitTopCardBounds
import SymmetricSubgroupAsymptotics.CentralIndexFourDerivedBound

/-! Pure cardinal installers for the SAME rank-five binary quotient. These
are internal inequalities, not new classification or published inputs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRankFiveCardUnitBounds

variable {Q : Type} [Group Q] [Finite Q]

private theorem derived_card_le_of_rank_five
    (hQ : IsPGroup 2 Q) (hrank : 5 ≤ MarkedC4.genRank Q)
    (d : ℕ) (hcard : Nat.card Q ≤ 32 * 2 ^ d) :
    Nat.card (commutator Q) ≤ 2 ^ d := by
  letI binaryRankFiveCardUnit_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha : 32 ≤ Nat.card (Abelianization Q) :=
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hrank).trans
      (pGroup_pow_genRank_le_abelianization_card 2 hQ)
  have hc := (commutator Q).card_eq_card_quotient_mul_card_subgroup
  change Nat.card Q = Nat.card (Abelianization Q) * Nat.card (commutator Q) at hc
  nlinarith

/-- The unit packet paid by4 derived bits and4 central bits. -/
theorem unit_of_card_le_fiveTwelve_center_le_sixteen
    (hQ : IsPGroup 2 Q) (hrank : 5 ≤ MarkedC4.genRank Q)
    (hcard : Nat.card Q ≤ 512) (hcenter : Nat.card (Subgroup.center Q) ≤ 16) :
    ∃ W : Subgroup Q, W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  exact normalF_unit_top_packet_of_card_bounds 4 4
    (derived_card_le_of_rank_five hQ hrank 4 (by norm_num; exact hcard))
    (by simpa using hcenter) (by decide) (by decide)

/-- The unit packet paid by6 derived bits and2 central bits. -/
theorem unit_of_card_le_twoThousand_center_le_four
    (hQ : IsPGroup 2 Q) (hrank : 5 ≤ MarkedC4.genRank Q)
    (hcard : Nat.card Q ≤ 2048) (hcenter : Nat.card (Subgroup.center Q) ≤ 4) :
    ∃ W : Subgroup Q, W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  exact normalF_unit_top_packet_of_card_bounds 6 2
    (derived_card_le_of_rank_five hQ hrank 6 (by norm_num; exact hcard))
    (by simpa using hcenter) (by decide) (by decide)

/-- The final large-section case pays7 derived bits and1 central bit. -/
theorem unit_of_card_le_fourThousand_center_le_two
    (hQ : IsPGroup 2 Q) (hrank : 5 ≤ MarkedC4.genRank Q)
    (hcard : Nat.card Q ≤ 4096) (hcenter : Nat.card (Subgroup.center Q) ≤ 2) :
    ∃ W : Subgroup Q, W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  exact normalF_unit_top_packet_of_card_bounds 7 1
    (derived_card_le_of_rank_five hQ hrank 7 (by norm_num; exact hcard))
    (by simpa using hcenter) (by decide) (by decide)

end SymmetricSubgroupAsymptotics.BinaryRankFiveCardUnitBounds
