import SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankThreeFrattiniHead
import SymmetricSubgroupAsymptotics.CFSGUnitaryCoprimeOuterCardinality
import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorOrdinaryRecurrence
import SymmetricSubgroupAsymptotics.PrimitiveSocleLeastIndexDegreeComparison
import SymmetricSubgroupAsymptotics.SmallSharpOuterPairNumerics

/-! The SAME actual binary rank-three unitary model has ordinary head4,
outer cardinal at most2, and actual minimum index at least8. Its literal
one-factor primitive recurrence therefore pays every action degree.
No generating-pair or new proper-index premise is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryBinaryRankThreeOrdinary
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (hq : q.order = 2) (e : D.Simple ≃* CFSG.Models.TwistedA 3 q) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedA 3 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedA 3 q) := Finite.of_equiv D.Simple e.toEquiv
  have hn : ¬ IsMulCommutative (CFSG.Models.TwistedA 3 q) := by
    intro h
    exact D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr h)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hm := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  have hfield := CFSGTwistedAUnitaryCoordinates.twistedA_admissible_order_power_le_leastProperIndex
    3 (by omega) q (by omega) ell hm
  have hell8 : 8 ≤ ell := by simpa only [hq] using hfield
  have hn8 := hell8.trans (PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell)
  have hhead : MarkedC4.genRank D.Simple ≤ 4 := by
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
    exact CFSGUnitaryBinaryRankThreeFrattiniHead.model_genRank_le_four q hq
  have hcard : Nat.card (Outer D.Simple) ≤ 2 := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGUnitaryCoprimeOuterCardinality.binary_rank_three_or_four_outer_card_le_two
      q hq 0 (Or.inl rfl) hn
  have hout : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 1 :=
    SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ 1 Nat.card_pos (by omega)
  have hG := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  have hfive : MarkedC4.genRank G ≤ 5 := by omega
  exact hfive.trans (SmallSharpOuterPairNumerics.five_le_ceiling (Nat.card X) (by omega))

theorem exists_generating_finset (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (hq : q.order = 2) (e : D.Simple ≃* CFSG.Models.TwistedA 3 q) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (genRank_le_ceiling D hk q hq e)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryBinaryRankThreeOrdinary
