import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorPairOrdinaryTail
import SymmetricSubgroupAsymptotics.TenGeneratorLogOrdinaryTail

/-! Ten actual generators of the same simple factor pay the original
one-factor coarse ordinary bound from degree64, with its literal outer
quotient retained. This makes no universal simple-generation assertion. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorTenOrdinaryTail
open PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_linear_log (hk : D.factorCount = 1)
    (hsimple : MarkedC4.genRank D.Simple ≤ 10)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    (MarkedC4.genRank G : ℝ) ≤ Real.logb 2 (Nat.card X : ℝ)+13 := by
  have hr : (MarkedC4.genRank D.Simple : ℝ) ≤ 10 := by exact_mod_cast hsimple
  have ho := PrimitiveSocleOneFactorPairOrdinaryTail.outerMultiplicity_le_log_degree
    D ell hell houter
  have hrec : (MarkedC4.genRank G : ℝ) ≤ (MarkedC4.genRank D.Simple : ℝ)+
      ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) := by
    exact_mod_cast PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  linarith only [hr,ho,hrec]

theorem genRank_le_ceiling (hk : D.factorCount = 1)
    (hsimple : MarkedC4.genRank D.Simple ≤ 10)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hn : 64 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  have h := ((genRank_le_linear_log D hk hsimple ell hell houter).trans
    (TenGeneratorLogOrdinaryTail.aggregate_le (Nat.card X) hn)).trans
    (Nat.le_ceil ((Nat.card X : ℝ)/Real.sqrt (Real.logb 2 (Nat.card X : ℝ))))
  change (MarkedC4.genRank G : ℝ) ≤
    (traceyPermutationGeneratorCeiling (Nat.card X) : ℝ) at h
  exact_mod_cast h

end SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorTenOrdinaryTail
