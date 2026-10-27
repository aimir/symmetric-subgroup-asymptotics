import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorTenOrdinaryFromThirtyTwo
import SymmetricSubgroupAsymptotics.ElevenGeneratorLogOrdinaryTail

/-! A proved11-generator simple head pays every actual one-factor primitive
degree at least32, retaining its SAME sufficient outer-index budget. The
head is not assumed to be two-generated and no classification is used.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorElevenOrdinaryFromThirtyTwo
open PrimitiveSocleRawStructure

private theorem outer_cardFactors_le_five (ell N : ℕ) (hN : 0<N)
    (houter : SufficientOuterOrderBudget ell N) (hell : 0<ell)
    (h64 : ell<64) : ArithmeticFunction.cardFactors N≤5 := by
  have hh := Real.logb_lt_logb (by norm_num : (1 : ℝ)<2)
    (by exact_mod_cast hell : (0 : ℝ)<ell)
    (by exact_mod_cast h64 : (ell : ℝ)<64)
  have hlog : Real.logb 2 (64 : ℝ)=6 := by
    rw [show (64 : ℝ)=2^6 by norm_num,Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)]
    norm_num
  rw [hlog] at hh
  apply SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow N 5 hN
  have hNR : (N : ℝ)<64 := by linarith only [houter.log_six,hh]
  exact_mod_cast hNR

private theorem outer_cardFactors_le_four (ell N : ℕ) (hN : 0<N)
    (houter : SufficientOuterOrderBudget ell N) (hell : 0<ell)
    (h33 : ell≤33) : ArithmeticFunction.cardFactors N≤4 := by
  have hp : ell^4≤2^21 :=
    (Nat.pow_le_pow_left h33 4).trans (by decide : (33 : ℕ)^4≤2^21)
  have hlog := IntegerLogSquareRootCeilingCertificate.log_upper ell 4 21 hell (by decide) hp
  apply SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow N 4 hN
  have hNR : (N : ℝ)<32 := by linarith only [houter.log_six,hlog]
  exact_mod_cast hNR

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_linear_log (hk : D.factorCount=1)
    (hsimple : MarkedC4.genRank D.Simple≤11)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    (MarkedC4.genRank G : ℝ)≤Real.logb 2 (Nat.card X : ℝ)+14 := by
  have hr : (MarkedC4.genRank D.Simple : ℝ)≤11 := by exact_mod_cast hsimple
  have ho := PrimitiveSocleOneFactorPairOrdinaryTail.outerMultiplicity_le_log_degree
    D ell hell houter
  have hrec : (MarkedC4.genRank G : ℝ)≤(MarkedC4.genRank D.Simple : ℝ)+
      ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) := by
    exact_mod_cast PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  linarith only [hr,ho,hrec]

theorem genRank_le_ceiling (hk : D.factorCount=1)
    (hsimple : MarkedC4.genRank D.Simple≤11)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hn : 32≤Nat.card X) :
    MarkedC4.genRank G≤traceyPermutationGeneratorCeiling (Nat.card X) := by
  by_cases h64 : 64≤Nat.card X
  · have h := ((genRank_le_linear_log D hk hsimple ell hell houter).trans
      (ElevenGeneratorLogOrdinaryTail.aggregate_le (Nat.card X) h64)).trans
      (Nat.le_ceil ((Nat.card X : ℝ)/Real.sqrt (Real.logb 2 (Nat.card X : ℝ))))
    change (MarkedC4.genRank G : ℝ)≤
      (traceyPermutationGeneratorCeiling (Nat.card X) : ℝ) at h
    exact_mod_cast h
  have hellr := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hell0 : 0<ell := by
    obtain ⟨H,hH,_⟩ := hell.1
    have hh := H.one_lt_index_of_ne_top hH
    omega
  have hsource := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  by_cases h34 : Nat.card X<34
  · have hOmega := outer_cardFactors_le_four ell (Nat.card (Outer D.Simple))
      Nat.card_pos houter hell0 (by omega)
    have h15 : MarkedC4.genRank G≤15 := by omega
    have hceil32 : 15≤traceyPermutationGeneratorCeiling 32 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 32 1 5 15
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact h15.trans (hceil32.trans
      (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) hn))
  · have hOmega := outer_cardFactors_le_five ell (Nat.card (Outer D.Simple))
      Nat.card_pos houter hell0 (by omega)
    have h16 : MarkedC4.genRank G≤16 := by omega
    have hceil34 : 16≤traceyPermutationGeneratorCeiling 34 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 34 8 41 16
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact h16.trans (hceil34.trans
      (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) (by omega)))

end SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorElevenOrdinaryFromThirtyTwo
