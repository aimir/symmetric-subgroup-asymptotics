import SymmetricSubgroupAsymptotics.TraceyOrdinarySporadicSmallRankResidual
import SymmetricSubgroupAsymptotics.CFSGYSectionGeneration
import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorTenOrdinaryTail

/-! The four original Y-derived central quotients already have proved
ordinary generating sets of size8,9,10,10. Their actual one-factor
primitive coarse ordinary branches are paid from degree64, retaining
the same outer quotient and the existing numerical callback. No
identification, order formula, two-generation or current Tracey input
is assumed for these literal models. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionOrdinaryTail
open PrimitiveSocleRawStructure CFSGReduction

def IsYSectionModel : CFSG.Sporadic → Prop
  | .fi22 | .fi23 | .fi24Prime | .babyMonster => True
  | _ => False

theorem ySection_generators (s : CFSG.Sporadic) (hs : IsYSectionModel s) :
    ∃ S : Finset s.Model, Subgroup.closure (S : Set s.Model) = ⊤ ∧ S.card ≤ 10 := by
  cases s <;> try { exact False.elim hs }
  case fi22 =>
    obtain ⟨S,hS,hcard⟩ := CFSGGeneration.fischer22_generators
    exact ⟨S,hS,hcard.trans (by decide)⟩
  case fi23 =>
    obtain ⟨S,hS,hcard⟩ := CFSGGeneration.fischer23_generators
    exact ⟨S,hS,hcard.trans (by decide)⟩
  case fi24Prime => exact CFSGGeneration.fischer24Prime_generators
  case babyMonster => exact CFSGGeneration.babyMonster_generators

theorem genRank_le_ceiling
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i)
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hk : D.factorCount = 1)
    (s : CFSG.Sporadic) (hs : IsYSectionModel s)
    (e : D.Simple ≃* (CFSG.Index.sporadic s).Model) (hn : 64 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : Finite (CFSG.Index.sporadic s).Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup (CFSG.Index.sporadic s).Model := e.symm.isSimpleGroup
  have hni : ¬ IsMulCommutative (CFSG.Index.sporadic s).Model := by
    intro hc
    exact D.noncommutative ((isMulCommutative_congr e).mpr hc)
  have hp : ModelSufficientSimpleIndexBounds (.sporadic s) :=
    remaining (.sporadic s) hni (by trivial)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hout := (sufficientSimpleIndexBounds_of_mulEquiv e hp ell hell).2
  have hsimple : MarkedC4.genRank D.Simple ≤ 10 := by
    let e0 : D.Simple ≃* s.Model := e
    letI : Finite s.Model := Finite.of_equiv D.Simple e0.toEquiv
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e0]
    obtain ⟨S,hS,hcard⟩ := ySection_generators s hs
    exact (MarkedC4.genRank_le hS).trans hcard
  exact PrimitiveSocleOneFactorTenOrdinaryTail.genRank_le_ceiling
    D hk hsimple ell hell hout hn

end SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionOrdinaryTail
