import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorTenOrdinaryFromThirtyTwo
import SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionOrdinaryTail

/-! A single family consumer for all four literal Y-derived FULL central
quotients. Their checked heads8/9/10/10 are bounded by ten and transported
to the SAME simple factor. The sufficient numerical packet is read only
from the unchanged callback already retained by the optional CFSG facade.
This is a conditional ordinary reduction, not a proof of that callback
or a new assumption for T1. No current-degree induction is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionOrdinaryFromThirtyTwo
open PrimitiveSocleRawStructure CFSGReduction

variable
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i)
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

include remaining

/-- Every one-factor primitive action of an actual member of the shared
Y-section family is paid from degree32, retaining its original quotient. -/
theorem genRank_le_ceiling (hk : D.factorCount = 1)
    (s : CFSG.Sporadic) (hs : PrimitiveSocleYSectionOrdinaryTail.IsYSectionModel s)
    (e : D.Simple ≃* (CFSG.Index.sporadic s).Model) (hn : 32 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : Finite (CFSG.Index.sporadic s).Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup (CFSG.Index.sporadic s).Model := e.symm.isSimpleGroup
  have hni : ¬ IsMulCommutative (CFSG.Index.sporadic s).Model := by
    intro hc
    exact D.noncommutative ((isMulCommutative_congr e).mpr hc)
  have hp : ModelSufficientSimpleIndexBounds (.sporadic s) :=
    remaining (.sporadic s) hni (by trivial)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have houter := (sufficientSimpleIndexBounds_of_mulEquiv e hp ell hell).2
  have hsimple : MarkedC4.genRank D.Simple ≤ 10 := by
    obtain ⟨S,hS,hcard⟩ := CFSGGeneration.generators_card_le_of_surjective
      e.symm.toMonoidHom e.symm.surjective
      (PrimitiveSocleYSectionOrdinaryTail.ySection_generators s hs)
    exact (MarkedC4.genRank_le hS).trans hcard
  exact PrimitiveSocleOneFactorTenOrdinaryFromThirtyTwo.genRank_le_ceiling
    D hk hsimple ell hell houter hn

theorem exists_generating_finset (hk : D.factorCount = 1)
    (s : CFSG.Sporadic) (hs : PrimitiveSocleYSectionOrdinaryTail.IsYSectionModel s)
    (e : D.Simple ≃* (CFSG.Index.sporadic s).Model) (hn : 32 ≤ Nat.card X) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S,hgen,hS.le.trans (genRank_le_ceiling remaining D hk s hs e hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionOrdinaryFromThirtyTwo
