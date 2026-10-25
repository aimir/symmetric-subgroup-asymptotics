import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorOrdinaryRecurrence
import SymmetricSubgroupAsymptotics.PrimitiveSocleLeastIndexDegreeComparison
import SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexBounds
import SymmetricSubgroupAsymptotics.ActualWreathUniformLocalOrderCost
import SymmetricSubgroupAsymptotics.CFSGCoarsePrimitiveNumerics
import SymmetricSubgroupAsymptotics.UnitLogOrdinaryGeneratorTail

/-! A displayed generating pair of the SAME simple socle factor pays the
one-factor ordinary tail. The original quotient is retained in the proved
recurrence before applying the actual factor's outer-order budget. No
permutation-generator theorem or global simple-generation input is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorPairOrdinaryTail
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem outerMultiplicity_le_log_degree
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    (ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) : ℝ) ≤
      Real.logb 2 (Nat.card X : ℝ) + 3 := by
  obtain ⟨H,hH,hindex⟩ := hell.1
  have hell0 : 0 < ell := by
    have hh := H.one_lt_index_of_ne_top hH
    omega
  have hellDegree := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  let L := Real.logb 2 (Nat.card X : ℝ)
  have hout := houter.log_six_of_le hell0 hellDegree
  have hLcard : L ≤ (Nat.card X : ℝ) := CFSGCoarsePrimitiveNumerics.logb_nat_le_nat _
  have hout8 : (Nat.card (Outer D.Simple) : ℝ) ≤ 8*(Nat.card X : ℝ) := by
    nlinarith only [hout,hLcard,(Nat.cast_nonneg (Nat.card X) : (0 : ℝ) ≤ Nat.card X)]
  have hdegree0 : (0 : ℝ) < Nat.card X := by
    exact_mod_cast (hell0.trans_le hellDegree)
  have houtLog : Real.logb 2 (Nat.card (Outer D.Simple) : ℝ) ≤ 3+L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (Nat.card_pos (α := Outer D.Simple))) hout8
    rw [Real.logb_mul (by norm_num : (8 : ℝ) ≠ 0) hdegree0.ne'] at hh
    have h8 : Real.logb 2 (8 : ℝ) = 3 := by
      rw [show (8 : ℝ) = (2 : ℝ)^3 by norm_num,Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      norm_num
    simpa only [h8] using hh
  have hOmega := (ActualWreathUniformLocalOrderCost.cardFactors_le_logb
    (Nat.card (Outer D.Simple)) (Nat.card_pos (α := Outer D.Simple)).ne').trans houtLog
  simpa only [L,add_comm] using hOmega

theorem genRank_le_linear_log (hk : D.factorCount = 1)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤)
    (hScard : S.card ≤ 2) (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    (MarkedC4.genRank G : ℝ) ≤ Real.logb 2 (Nat.card X : ℝ) + 5 := by
  have hsimple : MarkedC4.genRank D.Simple ≤ 2 := (MarkedC4.genRank_le hS).trans hScard
  have hsimpleR : (MarkedC4.genRank D.Simple : ℝ) ≤ 2 := by exact_mod_cast hsimple
  have hOmega := outerMultiplicity_le_log_degree D ell hell houter
  have hrec : (MarkedC4.genRank G : ℝ) ≤ (MarkedC4.genRank D.Simple : ℝ)+
      ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) := by
    exact_mod_cast PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  linarith only [hrec,hsimpleR,hOmega]

theorem genRank_le_ceiling (hk : D.factorCount = 1)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤)
    (hScard : S.card ≤ 2) (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hn : 32 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  have hh := genRank_le_linear_log D hk S hS hScard ell hell houter
  have hreal := (hh.trans (UnitLogOrdinaryGeneratorTail.aggregate_le (Nat.card X) hn)).trans
    (Nat.le_ceil ((Nat.card X : ℝ)/Real.sqrt (Real.logb 2 (Nat.card X : ℝ))))
  change (MarkedC4.genRank G : ℝ) ≤
    (traceyPermutationGeneratorCeiling (Nat.card X) : ℝ) at hreal
  exact_mod_cast hreal

theorem exists_generating_finset (hk : D.factorCount = 1)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤)
    (hScard : S.card ≤ 2) (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hn : 32 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (genRank_le_ceiling D hk S hS hScard ell hell houter hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorPairOrdinaryTail
