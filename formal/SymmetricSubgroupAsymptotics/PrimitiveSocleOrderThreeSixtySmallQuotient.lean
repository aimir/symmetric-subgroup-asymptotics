import SymmetricSubgroupAsymptotics.PrimitiveSocleActualQuotientGcdBudget
import SymmetricSubgroupAsymptotics.SmallSharpOuterPairNumerics

/-! The SAME actual socle quotient costs at most one ordinary generator
in degrees six or seven when the simple factor has order360 and outer
order at most four. This applies equally to literal alternating and PSL2
realizations, without identifying different models or substituting the
whole outer rank for the actual quotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleOrderThreeSixtySmallQuotient
open PrimitiveSocleRawStructure

private theorem gcd_le_two (o n : ℕ) (ho : 0 < o) (ho4 : o ≤ 4)
    (hn : n = 6 ∨ n = 7) : o.gcd (n.factorial/360) ≤ 2 := by
  rcases hn with rfl | rfl <;> interval_cases o <;> norm_num at *

theorem joint_cardFactors_le_one (o n : ℕ) (ho : 0 < o) (ho4 : o ≤ 4)
    (hn : n = 6 ∨ n = 7) :
    ArithmeticFunction.cardFactors (o.gcd (n.factorial/360)) ≤ 1 := by
  have hpos := Nat.gcd_pos_of_pos_left (n.factorial/360) ho
  have hbound := gcd_le_two o n ho ho4 hn
  exact SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ 1 hpos (by norm_num; omega)

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X)

theorem quotient_genRank_le_one (hk : D.factorCount = 1)
    (hn : Nat.card X = 6 ∨ Nat.card X = 7) (horder : Nat.card D.Simple = 360)
    (houter : Nat.card (Outer D.Simple) ≤ 4) :
    MarkedC4.genRank (G ⧸ finiteGroupSocle G) ≤ 1 := by
  have hh := joint_cardFactors_le_one (Nat.card (Outer D.Simple)) (Nat.card X)
    (Nat.card_pos (α := Outer D.Simple)) houter hn
  have hq := PrimitiveSocleActualQuotientGcdBudget.quotient_genRank_le_joint_cardFactors D hk
  rw [horder] at hq
  exact hq.trans hh

theorem genRank_le_three (hk : D.factorCount = 1)
    (hn : Nat.card X = 6 ∨ Nat.card X = 7) (horder : Nat.card D.Simple = 360)
    (houter : Nat.card (Outer D.Simple) ≤ 4) (hhead : MarkedC4.genRank D.Simple ≤ 2) :
    MarkedC4.genRank G ≤ 3 := by
  have hq := quotient_genRank_le_one D hk hn horder houter
  have hg := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_actual_quotient D hk
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleOrderThreeSixtySmallQuotient
