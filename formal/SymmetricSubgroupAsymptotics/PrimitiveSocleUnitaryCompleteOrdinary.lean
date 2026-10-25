import SymmetricSubgroupAsymptotics.CFSGUnitaryBoundedOrdinaryProfiles
import SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryOneFactorOrdinaryTail

/-! Every original unitary one-factor primitive ordinary degree. The
bounded range uses actual field-power index, Frattini/Sylow heads and
outer multiplicity; the large range uses the proved original Sylow tail.
No model callback, global permutation bound or induction is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryCompleteOrdinary
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1) (r : ℕ) (q : CFSG.PrimePower)
    (hr : 2 ≤ r) (hs : r = 2 → q.order ≠ 2)
    (e : D.Simple ≃* CFSG.Models.TwistedA r q) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  by_cases hlarge : 1024 ≤ Nat.card X
  · exact PrimitiveSocleUnitaryOneFactorOrdinaryTail.genRank_le_ceiling D hk r q hr hs e hlarge
  letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedA r q) := Finite.of_equiv D.Simple e.toEquiv
  have hn : ¬ IsMulCommutative (CFSG.Models.TwistedA r q) := by
    intro h
    exact D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr h)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hm := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  have hfield := CFSGTwistedAUnitaryCoordinates.twistedA_admissible_order_power_le_leastProperIndex
    r hr q hs ell hm
  have hdegree := hfield.trans (PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell)
  have hprofile := CFSGUnitaryBoundedOrdinaryProfiles.model_cost_le_ceiling r q hr hs hn
    (Nat.card X) hdegree (by omega)
  have hc := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e,CFSGReduction.outer_card_congr e] at hc
  exact hc.trans hprofile

theorem exists_generating_finset (hk : D.factorCount = 1) (r : ℕ) (q : CFSG.PrimePower)
    (hr : 2 ≤ r) (hs : r = 2 → q.order ≠ 2)
    (e : D.Simple ≃* CFSG.Models.TwistedA r q) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (genRank_le_ceiling D hk r q hr hs e)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryCompleteOrdinary
