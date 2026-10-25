import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorTripleOrdinaryTail

/-! A uniform finite band for a three-generator simple socle. The actual
outer order is bounded before taking its logarithm, avoiding the loose
linear-log envelope. No ordinary permutation-generator input is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleSmallDegreeTripleOrdinary
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1)
    (hsimple : MarkedC4.genRank D.Simple ≤ 3)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hlo : 20 ≤ Nat.card X) (hhi : Nat.card X ≤ 31) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  have hell0 : 0 < ell := by
    obtain ⟨H, hH, he⟩ := hell.1
    have h := H.one_lt_index_of_ne_top hH
    omega
  have hdegree := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hLpos : 0 < Real.logb 2 (Nat.card X : ℝ) :=
    Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < Nat.card X by omega))
  have h32 : Real.logb 2 (32 : ℝ) = 5 := by
    rw [show (32 : ℝ) = 2^5 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  have hL : Real.logb 2 (Nat.card X : ℝ) ≤ 5 := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (show (0 : ℝ) < (Nat.card X : ℝ) by exact_mod_cast (show 0 < Nat.card X by omega))
      (show (Nat.card X : ℝ) ≤ (32 : ℝ) by exact_mod_cast (show Nat.card X ≤ 32 by omega))
    simpa only [h32] using h
  have hout : (Nat.card (Outer D.Simple) : ℝ) ≤ 32 := by
    have h := houter.log_six_of_le hell0 hdegree
    linarith
  have hlogOut : Real.logb 2 (Nat.card (Outer D.Simple) : ℝ) ≤ 5 := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (Nat.card_pos (α := Outer D.Simple))) hout
    simpa only [h32] using h
  have hOmega := (ActualWreathUniformLocalOrderCost.cardFactors_le_logb
    (Nat.card (Outer D.Simple)) (Nat.card_pos (α := Outer D.Simple)).ne').trans hlogOut
  have hr : (MarkedC4.genRank D.Simple : ℝ) ≤ 3 := by exact_mod_cast hsimple
  have hrec : (MarkedC4.genRank G : ℝ) ≤ (MarkedC4.genRank D.Simple : ℝ) +
      ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) := by
    exact_mod_cast PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  have hgen : (MarkedC4.genRank G : ℝ) ≤ 8 := by linarith
  have hsqrt : Real.sqrt (Real.logb 2 (Nat.card X : ℝ)) ≤ (5/2 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hbudget : (8 : ℝ) ≤ (Nat.card X : ℝ) /
      Real.sqrt (Real.logb 2 (Nat.card X : ℝ)) := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hLpos)).mpr
    have hcard : (20 : ℝ) ≤ Nat.card X := by exact_mod_cast hlo
    linarith
  have h := ((hgen.trans hbudget).trans
    (Nat.le_ceil ((Nat.card X : ℝ) / Real.sqrt (Real.logb 2 (Nat.card X : ℝ)))))
  change (MarkedC4.genRank G : ℝ) ≤
    (traceyPermutationGeneratorCeiling (Nat.card X) : ℝ) at h
  exact_mod_cast h

end SymmetricSubgroupAsymptotics.PrimitiveSocleSmallDegreeTripleOrdinary
