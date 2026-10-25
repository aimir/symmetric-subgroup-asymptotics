import SymmetricSubgroupAsymptotics.GoodSylowPrimeOrderOrdinaryGenerators

/-! Retain the actual ordinary rank of a selected Sylow, rather than
replacing it by its order multiplicity. Surjective transport retains the
literal derived/central-quotient map used by original models. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.GoodSylowSelectedRankOrdinaryGenerators

variable {G : Type} [Group G] [Finite G]

theorem genRank_le_selected (p : ℕ) (hgood : CFSGReduction.GoodSylowPrime G p)
    (Q : Sylow p G) : MarkedC4.genRank G ≤ MarkedC4.genRank Q+1 := by
  obtain ⟨hp,P,g,_,hgen⟩ := hgood
  letI : Fact p.Prime := ⟨hp⟩
  have he := CoprimeNilpotentProductGenerators.genRank_mulEquiv (P.equiv Q)
  have hpair := TwoConjugateSubgroupsOrdinaryGenerators.genRank_le_add_one (P : Subgroup G) g hgen
  rwa [he] at hpair

theorem genRank_le_of_surjective {M : Type} [Group M]
    (p : ℕ) (hgood : CFSGReduction.GoodSylowPrime G p) (Q : Sylow p G)
    (f : G →* M) (hf : Function.Surjective f) :
    MarkedC4.genRank M ≤ MarkedC4.genRank Q+1 := by
  obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := G)
  have hT : Subgroup.closure ((S.image f : Finset M) : Set M) = ⊤ := by
    have he := congrArg (Subgroup.map f) hgen
    simpa only [Finset.coe_image,MonoidHom.map_closure,
      Subgroup.map_top_of_surjective f hf] using he
  exact (MarkedC4.genRank_le hT).trans
    (Finset.card_image_le.trans (hcard.le.trans (genRank_le_selected p hgood Q)))

end SymmetricSubgroupAsymptotics.GoodSylowSelectedRankOrdinaryGenerators
