import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorTenOrdinaryFromThirtyTwo

/-! Six actual simple-factor generators pay every one-factor primitive
action from degree17, under the SAME already-retained outer budget.
Only its stated small-index and log-six fields are used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorSixOrdinaryFromSeventeen
open PrimitiveSocleRawStructure

private theorem log_index_lt_five (ell : ℕ) (hell : 0 < ell) (h32 : ell < 32) :
    Real.logb 2 ell < 5 := by
  have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hell : (0 : ℝ) < ell)
    (by exact_mod_cast h32 : (ell : ℝ) < 32)
  have hlog : Real.logb 2 (32 : ℝ)=5 := by
    rw [show (32 : ℝ)=2^5 by norm_num,Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  rwa [hlog] at h

private theorem outer_cardFactors_le_four (ell N : ℕ) (hN : 0 < N)
    (houter : SufficientOuterOrderBudget ell N) (hell : 0 < ell) (h32 : ell < 32) :
    ArithmeticFunction.cardFactors N ≤ 4 := by
  have hlog := log_index_lt_five ell hell h32
  apply SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow N 4 hN
  have hNR : (N : ℝ) < 32 := by linarith only [houter.log_six,hlog]
  exact_mod_cast hNR

private theorem outer_cardFactors_le_three (ell N : ℕ) (hN : 0 < N)
    (houter : SufficientOuterOrderBudget ell N) (hell : 0 < ell) (h27 : ell < 27) :
    ArithmeticFunction.cardFactors N ≤ 3 := by
  have hlog := log_index_lt_five ell hell (by omega)
  have hsmall := houter.log_three_of_small h27
  apply SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow N 3 hN
  have hNR : (N : ℝ) < 16 := by linarith only [hsmall,hlog]
  exact_mod_cast hNR

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount=1)
    (hsimple : MarkedC4.genRank D.Simple ≤ 6)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hn : 17 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  by_cases h32 : 32 ≤ Nat.card X
  · exact PrimitiveSocleOneFactorTenOrdinaryFromThirtyTwo.genRank_le_ceiling
      D hk (by omega) ell hell houter h32
  have hellr := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hell0 : 0 < ell := by
    obtain ⟨H,hH,_⟩ := hell.1
    have hh := H.one_lt_index_of_ne_top hH
    omega
  have hsource := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  by_cases h27 : Nat.card X < 27
  · have hOmega := outer_cardFactors_le_three ell (Nat.card (Outer D.Simple))
      Nat.card_pos houter hell0 (by omega)
    have h9 : MarkedC4.genRank G ≤ 9 := by omega
    have hceil17 : 9 ≤ traceyPermutationGeneratorCeiling 17 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 17 4 17 9
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact h9.trans (hceil17.trans
      (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) hn))
  · have hOmega := outer_cardFactors_le_four ell (Nat.card (Outer D.Simple))
      Nat.card_pos houter hell0 (by omega)
    have h10 : MarkedC4.genRank G ≤ 10 := by omega
    have hceil19 : 10 ≤ traceyPermutationGeneratorCeiling 19 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 19 4 17 10
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact h10.trans (hceil19.trans
      (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) (by omega)))

end SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorSixOrdinaryFromSeventeen
