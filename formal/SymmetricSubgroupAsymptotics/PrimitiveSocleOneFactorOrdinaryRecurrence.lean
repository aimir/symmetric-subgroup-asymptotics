import SymmetricSubgroupAsymptotics.PrimitiveSocleStrictOuterOrdinaryRecurrence
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawOneFactor

/-! The actual one-factor socle costs ONE copy of the original simple
ordinary rank. The quotient is retained before its genuine outer-order
multiplicity estimate is applied. This permits actual model generator
sets to be used without a global simple two-generation premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorOrdinaryRecurrence
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_simple_add_actual_quotient (hk : D.factorCount = 1) :
    MarkedC4.genRank G ≤ MarkedC4.genRank D.Simple+
      MarkedC4.genRank (G ⧸ finiteGroupSocle G) := by
  have he := CoprimeNilpotentProductGenerators.genRank_mulEquiv (D.oneFactorEquiv hk)
  have hh := MarkedC4.genRank_le_of_normal (finiteGroupSocle G)
  simpa only [he] using hh

theorem genRank_le_simple_add_outer_multiplicity (hk : D.factorCount = 1) :
    MarkedC4.genRank G ≤ MarkedC4.genRank D.Simple+
      ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) := by
  have hquot := PrimitiveSocleStrictOuterOrdinaryRecurrence.quotient_genRank_le_outer_multiplicity D
  simp only [hk,Nat.one_mul,Nat.factorial_one,ArithmeticFunction.cardFactors_one,add_zero] at hquot
  exact (genRank_le_simple_add_actual_quotient D hk).trans (Nat.add_le_add_left hquot _)

theorem exists_generating_finset_of_simple_generators (hk : D.factorCount = 1)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ S.card+ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  have hh := (genRank_le_simple_add_outer_multiplicity D hk).trans
    (Nat.add_le_add_right (MarkedC4.genRank_le hS) _)
  exact ⟨U,hgen,hU.le.trans hh⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorOrdinaryRecurrence
