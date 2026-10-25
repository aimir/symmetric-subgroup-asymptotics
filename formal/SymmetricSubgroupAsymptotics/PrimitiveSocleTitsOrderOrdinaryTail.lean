import SymmetricSubgroupAsymptotics.TraceyOrdinaryTitsMonsterResidual
import SymmetricSubgroupAsymptotics.CFSGReeFFourWeightedFixedOrderUpper
import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators

/-! The actual original Tits order upper bound 2^26 pays its one-factor
primitive ordinary tail from degree128. No Tits generating-pair or
known-order assertion is assumed. Its sufficient outer budget is read
from the SAME numerical callback already retained by the optional T1
facade. This does not discharge that callback or the good-Sylow task. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleTitsOrderOrdinaryTail
open PrimitiveSocleRawStructure CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem simple_genRank_le_twentySix (e : D.Simple ≃* CFSG.Models.Tits) :
    MarkedC4.genRank D.Simple ≤ 26 := by
  apply FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow D.Simple 26
  rw [Nat.card_congr e.toEquiv]
  simpa only [Nat.mul_zero,Nat.zero_add,Nat.pow_one] using
    CFSGReeFFourWeightedFixedOrderUpper.original_ree_order_le 0

theorem genRank_le_ceiling
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i)
    (hk : D.factorCount = 1) (e : D.Simple ≃* CFSG.Index.tits.Model)
    (hn : 128 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : Finite CFSG.Index.tits.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup CFSG.Index.tits.Model := e.symm.isSimpleGroup
  have hni : ¬ IsMulCommutative CFSG.Index.tits.Model := by
    intro hc
    exact D.noncommutative ((isMulCommutative_congr e).mpr hc)
  have hp : ModelSufficientSimpleIndexBounds .tits := remaining .tits hni (by trivial)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hout := (sufficientSimpleIndexBounds_of_mulEquiv e hp ell hell).2
  have hsimple := simple_genRank_le_twentySix D e
  have hsr : (MarkedC4.genRank D.Simple : ℝ) ≤ 26 := by exact_mod_cast hsimple
  have ho := PrimitiveSocleOneFactorPairOrdinaryTail.outerMultiplicity_le_log_degree D ell hell hout
  have hrec : (MarkedC4.genRank G : ℝ) ≤ (MarkedC4.genRank D.Simple : ℝ)+
      ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) := by
    exact_mod_cast PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  have hlower : (7 : ℝ) ≤ Real.logb 2 (Nat.card X : ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 128) (by exact_mod_cast hn : (128 : ℝ) ≤ Nat.card X)
    have h128 : Real.logb 2 (128 : ℝ) = 7 := by
      rw [show (128 : ℝ) = (2 : ℝ)^7 by norm_num,Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      norm_num
    rwa [h128] at hh
  have hlinear : (MarkedC4.genRank G : ℝ) ≤ 5*Real.logb 2 (Nat.card X : ℝ)+3 := by
    linarith only [hsr,ho,hrec,hlower]
  have h := (hlinear.trans (LinearLogOrdinaryGeneratorTail.aggregate_le (Nat.card X) hn)).trans
    (Nat.le_ceil ((Nat.card X : ℝ)/Real.sqrt (Real.logb 2 (Nat.card X : ℝ))))
  change (MarkedC4.genRank G : ℝ) ≤
    (traceyPermutationGeneratorCeiling (Nat.card X) : ℝ) at h
  exact_mod_cast h

end SymmetricSubgroupAsymptotics.PrimitiveSocleTitsOrderOrdinaryTail
