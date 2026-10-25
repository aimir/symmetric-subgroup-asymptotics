import SymmetricSubgroupAsymptotics.PrimitiveSocleSmallDegreeTripleOrdinary
import SymmetricSubgroupAsymptotics.TraceyOrdinarySporadicSmallRankResidual
import SymmetricSubgroupAsymptotics.CFSGJ4TwentyThreeDivisor

/-! The literal order23 witness excludes small actual J4 socle actions.
The sharper finite-band outer estimate and existing tail therefore pay
every actual one-factor primitive J4 coarse-generator branch. The SAME
numerical callback is retained; small imprimitive J4 components are not
claimed closed here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleJFourCompleteOrdinary
open PrimitiveSocleRawStructure CFSGReduction

variable
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i)
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X)

include remaining in
theorem genRank_le_ceiling (hk : D.factorCount = 1)
    (e : D.Simple ≃* (CFSG.Index.sporadic .j4).Model) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  by_cases hlarge : 32 ≤ Nat.card X
  · exact TraceyOrdinarySporadicSmallRankResidual.j4_genRank_le_ceiling remaining D hk e hlarge
  have hsmall : 23 ≤ Nat.card X := by
    by_contra h
    exact CFSGJ4TwentyThreeDivisor.not_j4_of_degree_le_twentyTwo D (by omega) e
  letI : Finite (CFSG.Index.sporadic .j4).Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup (CFSG.Index.sporadic .j4).Model := e.symm.isSimpleGroup
  have hni : ¬ IsMulCommutative (CFSG.Index.sporadic .j4).Model := by
    intro hc
    exact D.noncommutative ((isMulCommutative_congr e).mpr hc)
  have hp : ModelSufficientSimpleIndexBounds (.sporadic .j4) :=
    remaining (.sporadic .j4) hni (by trivial)
  obtain ⟨ell, hell⟩ := exists_leastProperIndex D.Simple
  have hout := (sufficientSimpleIndexBounds_of_mulEquiv e hp ell hell).2
  have hsimple : MarkedC4.genRank D.Simple ≤ 3 := by
    let e0 : D.Simple ≃* CFSG.Models.Presentations.J4.Model := e
    letI : Finite CFSG.Models.Presentations.J4.Model := Finite.of_equiv D.Simple e0.toEquiv
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e0]
    obtain ⟨S,hS,hcard⟩ := CFSGGeneration.j4_three_generators
    exact (MarkedC4.genRank_le hS).trans hcard
  exact PrimitiveSocleSmallDegreeTripleOrdinary.genRank_le_ceiling D hk hsimple ell hell hout
    (by omega) (by omega)

end SymmetricSubgroupAsymptotics.PrimitiveSocleJFourCompleteOrdinary
