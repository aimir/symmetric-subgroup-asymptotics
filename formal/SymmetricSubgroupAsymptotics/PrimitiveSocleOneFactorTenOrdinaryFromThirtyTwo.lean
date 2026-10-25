import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorTenOrdinaryTail
import SymmetricSubgroupAsymptotics.TraceyCoarseCeilingMonotonicity
import SymmetricSubgroupAsymptotics.SmallSharpOuterPairNumerics

/-! Ten genuine generators of the SAME simple factor pay a one-factor
primitive action from degree32. The bounded band retains the actual
outer quotient: its sufficient least-index budget gives Omega<=5,
so the source rank is at most15, paid by the genuine rounded ceiling
at32. The existing real tail is reused from64. No model, classification,
Tracey/MN input or fitted endpoint is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorTenOrdinaryFromThirtyTwo
open PrimitiveSocleRawStructure

private theorem outer_cardFactors_le_five (ell N : ℕ) (hN : 0 < N)
    (houter : SufficientOuterOrderBudget ell N) (hell : 0 < ell)
    (h64 : ell < 64) : ArithmeticFunction.cardFactors N ≤ 5 := by
  have hh := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hell : (0 : ℝ) < ell)
    (by exact_mod_cast h64 : (ell : ℝ) < 64)
  have hlog : Real.logb 2 (64 : ℝ) = 6 := by
    rw [show (64 : ℝ) = 2^6 by norm_num,Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  rw [hlog] at hh
  apply SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow N 5 hN
  have hNR : (N : ℝ) < 64 := by linarith only [houter.log_six,hh]
  exact_mod_cast hNR

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

/-- The explicit outer budget belongs to this factor's actual least index.
No current-degree induction or whole permutation-generator bound is used. -/
theorem genRank_le_ceiling (hk : D.factorCount = 1)
    (hsimple : MarkedC4.genRank D.Simple ≤ 10)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hn : 32 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  by_cases h64 : 64 ≤ Nat.card X
  · exact PrimitiveSocleOneFactorTenOrdinaryTail.genRank_le_ceiling
      D hk hsimple ell hell houter h64
  · have hellr := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
    have hell0 : 0 < ell := by
      obtain ⟨H,hH,_⟩ := hell.1
      have hh := H.one_lt_index_of_ne_top hH
      omega
    have hOmega := outer_cardFactors_le_five ell (Nat.card (Outer D.Simple))
      Nat.card_pos houter hell0 (by omega)
    have hsource := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
    have h15 : MarkedC4.genRank G ≤ 15 := by omega
    have hceil32 : 15 ≤ traceyPermutationGeneratorCeiling 32 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 32 1 5 15
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact h15.trans (hceil32.trans
      (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) hn))

theorem exists_generating_finset (hk : D.factorCount = 1)
    (hsimple : MarkedC4.genRank D.Simple ≤ 10)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hn : 32 ≤ Nat.card X) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S,hgen,hS.le.trans (genRank_le_ceiling D hk hsimple ell hell houter hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorTenOrdinaryFromThirtyTwo
