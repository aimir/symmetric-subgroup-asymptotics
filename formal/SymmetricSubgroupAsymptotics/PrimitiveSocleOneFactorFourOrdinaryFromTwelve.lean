import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorSixOrdinaryFromSeventeen

/-! Four actual simple-factor generators pay the original one-factor
primitive action from degree12 under its unchanged sufficient outer
budget. The only new interval is12..16; the six-head theorem pays the rest. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorFourOrdinaryFromTwelve
open PrimitiveSocleRawStructure

theorem genRank_le_ceiling
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (hsimple : MarkedC4.genRank D.Simple ≤ 4)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hn : 12 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  by_cases h17 : 17 ≤ Nat.card X
  · exact PrimitiveSocleOneFactorSixOrdinaryFromSeventeen.genRank_le_ceiling
      D hk (by omega) ell hell houter h17
  have hellr := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hell0 : 0 < ell := by
    obtain ⟨H,hH,_⟩ := hell.1
    have hh := H.one_lt_index_of_ne_top hH
    omega
  have hlog := IntegerLogSquareRootCeilingCertificate.log_upper ell 1 5 hell0
    (by decide) (by simpa using (show ell ≤ 32 by omega))
  norm_num at hlog
  have hsmall := houter.log_three_of_small (by omega : ell < 27)
  have hOmega : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 3 := by
    apply SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ 3 Nat.card_pos
    have hNR : (Nat.card (Outer D.Simple) : ℝ) < 16 := by linarith only [hsmall,hlog]
    exact_mod_cast hNR
  have hsource := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  have h7 : MarkedC4.genRank G ≤ 7 := by omega
  have hceil12 : 7 ≤ traceyPermutationGeneratorCeiling 12 :=
    IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 12 3 11 7
      (by decide) (by decide) (by decide) (by decide) (by decide)
  exact h7.trans (hceil12.trans
    (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) hn))

end SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorFourOrdinaryFromTwelve
