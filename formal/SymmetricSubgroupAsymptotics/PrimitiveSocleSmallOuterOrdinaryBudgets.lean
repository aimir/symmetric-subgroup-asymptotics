import SymmetricSubgroupAsymptotics.PrimitiveSocleOrderThreeSixtySmallQuotient
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.CFSGAlternatingOuterBound

/-! Small outer ORDERS pay genuine ordinary ranks. The exceptional
alternating-six outer bound uses the SAME faithful-action quotient gcd,
so its full outer rank is not charged to a quotient of order at most two.
No two-generation assertion is postulated: the displayed head budget is
an explicit local input, supplied by proved model generators downstream. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleSmallOuterOrdinaryBudgets
open PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X)

omit [FaithfulSMul G X] in
theorem genRank_le_three_of_outer_le_two (hk : D.factorCount = 1)
    (hhead : MarkedC4.genRank D.Simple ≤ 2) (houter : Nat.card (Outer D.Simple) ≤ 2) :
    MarkedC4.genRank G ≤ 3 := by
  have ho := SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow
    (Nat.card (Outer D.Simple)) 1 (Nat.card_pos (α := Outer D.Simple)) (by norm_num; omega)
  have hg := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  omega

omit [FaithfulSMul G X] in
theorem genRank_le_four_of_outer_le_four (hk : D.factorCount = 1)
    (hhead : MarkedC4.genRank D.Simple ≤ 2) (houter : Nat.card (Outer D.Simple) ≤ 4) :
    MarkedC4.genRank G ≤ 4 := by
  have ho := SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow
    (Nat.card (Outer D.Simple)) 2 (Nat.card_pos (α := Outer D.Simple)) (by norm_num; omega)
  have hg := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  omega

theorem genRank_le_three_of_alternating (hk : D.factorCount = 1)
    (hn : Nat.card X = 6 ∨ Nat.card X = 7) (hhead : MarkedC4.genRank D.Simple ≤ 2)
    (m : ℕ) (hm : 5 ≤ m) (e : D.Simple ≃* alternatingGroup (Fin m)) :
    MarkedC4.genRank G ≤ 3 := by
  by_cases h6 : m = 6
  · subst m
    have horder : Nat.card D.Simple = 360 := by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      decide
    have ho : Nat.card (Outer D.Simple) ≤ 4 := by
      rw [CFSGReduction.outer_card_congr e]
      exact CFSGAlternatingOuterBound.outer_card_le_four 6 hm
    exact PrimitiveSocleOrderThreeSixtySmallQuotient.genRank_le_three D hk hn horder ho hhead
  · have ho : Nat.card (Outer D.Simple) ≤ 2 := by
      rw [CFSGReduction.outer_card_congr e,
        CFSGAlternatingOuterBound.outer_card_eq_two_of_ne_six m hm h6]
    exact genRank_le_three_of_outer_le_two D hk hhead ho

end SymmetricSubgroupAsymptotics.PrimitiveSocleSmallOuterOrdinaryBudgets
