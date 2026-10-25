import SymmetricSubgroupAsymptotics.PrimitiveSocleModelRootStarOrdinaryTail
import SymmetricSubgroupAsymptotics.CFSGNormTwoPrimePowerOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGExceptionalLongChainStarIndex
import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergIndex
import SymmetricSubgroupAsymptotics.CFSGExceptionalOuterBudget

/-! All degrees of the same original E6/E7/E8 models in the one-factor
ordinary bound. Their actual simple-root generators, long-chain stars,
and outer budgets are proved model facts. Their prime-field Heisenberg
subgroups force every proper index above 2048, so the tail threshold is
internal and no current-degree induction is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleExceptionalEOneFactorOrdinaryGenerators
open PrimitiveSocleRawStructure CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormTwoBases
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₇) := Classical.decEq _
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₈) := Classical.decEq _

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem typeE6_genRank_le_ceiling (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.E6 q) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.E6 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.E6 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  obtain ⟨ell, hell⟩ := exists_leastProperIndex D.Simple
  have hellM := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  obtain ⟨H, hH, he⟩ := hellM.1
  have hdegree : 128 ≤ Nat.card X := by
    have hindex : 2048 ≤ ell := he ▸ CFSGReduction.typeE6_2048_le_index q H hH
    have hh := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
    omega
  apply PrimitiveSocleModelRootStarOrdinaryTail.genRank_le_ceiling
    D hk q 6 (by decide) e ?_ ?_ ?_ hdegree
  · exact CFSGNormTwoPrimePowerOrdinaryGenerators.exists_generating_finset_of_cartan_eq
      CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos q E6_cartan 0
  · intro K hK
    exact CFSGReduction.typeE6_field_fifth_le_index q K hK
  · intro i hi
    exact CFSGExceptionalOuterBudget.serreTypeE6_sufficient_outer_budget q.Field q.prime i hi

theorem typeE6_exists_generating_finset (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.E6 q) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U, hU, hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U, hgen, hU.le.trans (typeE6_genRank_le_ceiling D hk q e)⟩

theorem typeE7_genRank_le_ceiling (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.E7 q) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.E7 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.E7 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  obtain ⟨ell, hell⟩ := exists_leastProperIndex D.Simple
  have hellM := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  obtain ⟨H, hH, he⟩ := hellM.1
  have hdegree : 128 ≤ Nat.card X := by
    have hindex : 2048 ≤ ell := he ▸ CFSGReduction.typeE7_2048_le_index q H hH
    have hh := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
    omega
  apply PrimitiveSocleModelRootStarOrdinaryTail.genRank_le_ceiling
    D hk q 7 (by decide) e ?_ ?_ ?_ hdegree
  · exact CFSGNormTwoPrimePowerOrdinaryGenerators.exists_generating_finset_of_cartan_eq
      CartanMatrix.E₇ CartanMatrix.E₇_diag CartanMatrix.E₇_transpose
      E7_positive_definite CartanMatrix.E₇_off_diag_nonpos q E7_cartan 0
  · intro K hK
    exact CFSGReduction.typeE7_field_sixth_le_index q K hK
  · intro i hi
    exact CFSGExceptionalOuterBudget.serreTypeE7_sufficient_outer_budget q.Field q.prime i hi

theorem typeE7_exists_generating_finset (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.E7 q) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U, hU, hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U, hgen, hU.le.trans (typeE7_genRank_le_ceiling D hk q e)⟩

theorem typeE8_genRank_le_ceiling (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.E8 q) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.E8 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.E8 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  obtain ⟨ell, hell⟩ := exists_leastProperIndex D.Simple
  have hellM := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  obtain ⟨H, hH, he⟩ := hellM.1
  have hdegree : 128 ≤ Nat.card X := by
    have hindex : 2048 ≤ ell := he ▸ CFSGReduction.typeE8_2048_le_index q H hH
    have hh := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
    omega
  apply PrimitiveSocleModelRootStarOrdinaryTail.genRank_le_ceiling
    D hk q 8 (by decide) e ?_ ?_ ?_ hdegree
  · exact CFSGNormTwoPrimePowerOrdinaryGenerators.exists_generating_finset_of_cartan_eq
      CartanMatrix.E₈ CartanMatrix.E₈_diag CartanMatrix.E₈_transpose
      E8_positive_definite CartanMatrix.E₈_off_diag_nonpos q E8_cartan 0
  · intro K hK
    exact CFSGReduction.typeE8_field_seventh_le_index q K hK
  · intro i hi
    exact CFSGExceptionalOuterBudget.serreTypeE8_sufficient_outer_budget q.Field q.prime i hi

theorem typeE8_exists_generating_finset (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.E8 q) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U, hU, hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U, hgen, hU.le.trans (typeE8_genRank_le_ceiling D hk q e)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleExceptionalEOneFactorOrdinaryGenerators
