import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorFourOrdinaryFromTwelve
import SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionOrdinaryTail
import SymmetricSubgroupAsymptotics.CFSGYCoprimeOrdinaryGenerators

/-! Actual coprime-arm generation pays every one-factor primitive
Y-section model from degree12. Its source is the original derived FULL
central quotient, and its numerical callback is the existing one. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionOrdinaryFromTwelve
open PrimitiveSocleRawStructure CFSGReduction

theorem ySection_four_generators (s : CFSG.Sporadic)
    (hs : PrimitiveSocleYSectionOrdinaryTail.IsYSectionModel s) :
    ∃ S : Finset s.Model, Subgroup.closure (S : Set s.Model)=⊤ ∧ S.card ≤ 4 := by
  exact CFSGYCoprimeOrdinaryGenerators.y_model_generators s hs

theorem genRank_le_ceiling
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i)
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (s : CFSG.Sporadic) (hs : PrimitiveSocleYSectionOrdinaryTail.IsYSectionModel s)
    (e : D.Simple ≃* (CFSG.Index.sporadic s).Model) (hn : 12 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : Finite (CFSG.Index.sporadic s).Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup (CFSG.Index.sporadic s).Model := e.symm.isSimpleGroup
  have hni : ¬IsMulCommutative (CFSG.Index.sporadic s).Model := by
    intro hc
    exact D.noncommutative ((isMulCommutative_congr e).mpr hc)
  have hp : ModelSufficientSimpleIndexBounds (.sporadic s) :=
    remaining (.sporadic s) hni (by trivial)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have houter := (sufficientSimpleIndexBounds_of_mulEquiv e hp ell hell).2
  have hsimple : MarkedC4.genRank D.Simple ≤ 4 := by
    obtain ⟨S,hS,hcard⟩ := CFSGGeneration.generators_card_le_of_surjective
      e.symm.toMonoidHom e.symm.surjective (ySection_four_generators s hs)
    exact (MarkedC4.genRank_le hS).trans hcard
  exact PrimitiveSocleOneFactorFourOrdinaryFromTwelve.genRank_le_ceiling
    D hk hsimple ell hell houter hn

end SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionOrdinaryFromTwelve
