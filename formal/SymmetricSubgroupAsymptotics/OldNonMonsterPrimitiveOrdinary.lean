import SymmetricSubgroupAsymptotics.PrimitiveOrdinaryLieCFSGReduction
import SymmetricSubgroupAsymptotics.TraceyOrdinaryRetainedIndexResidual
import SymmetricSubgroupAsymptotics.PrimitiveSocleTitsCompleteOrdinary
import SymmetricSubgroupAsymptotics.PrimitiveSocleJFourCompleteOrdinary
import SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionOrdinaryFromSeventeen
import SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionSmallActionExclusion
import SymmetricSubgroupAsymptotics.SporadicPairAllDegreeOrdinary

/-! Actual per-model coarse primitive frontend extracted from the checked
old-family consumers. There is NO old classification hypothesis. The retained
simple-index numerical input is the existing public residual input, not a new
ordinary-rank/census callback. Its model is always selected by the explicit e.
The historical old Monster label is excluded. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OldNonMonsterPrimitiveOrdinary
open PrimitiveSocleRawStructure CFSGReduction TraceyStrictlySmallerTransitiveActions
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)
open PrimitiveSocleYSectionOrdinaryTail (IsYSectionModel)
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction (RemainingModel)

variable (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
    ¬IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
      ModelBoundsAfterReeFFourIndexSquare i)

include remaining in
/-- This is an actual-model theorem, prior to any classification dispatch. -/
theorem model_packet (j : CFSG.Index) [Finite j.Model] [IsSimpleGroup j.Model]
    (hn : ¬IsMulCommutative j.Model) : ModelSufficientSimpleIndexBounds j := by
  rcases CFSGSimpleIndexPacketOrTitsSporadic.model_packet_or_remaining j hn with hp | hj
  · exact hp
  · cases j <;> try { exact False.elim hj }
    case tits => exact remaining .tits hn (by trivial)
    case sporadic s hfinite hsimple => exact remaining (.sporadic s) hn (by trivial)

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X)

include remaining in
theorem genRank_le_ceiling (j : CFSG.Index) (hnot : j≠.sporadic .monster)
    (e : D.Simple ≃* j.Model) (hbelow : SmallerTransitiveRankBound (Nat.card X)) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : Finite j.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup j.Model := e.symm.isSimpleGroup
  have hnon : ¬IsMulCommutative j.Model :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  by_cases hpair : PairFamily j
  · exact PrimitiveSoclePairFamiliesCompleteOrdinary.genRank_le_ceiling D j hpair e hbelow
  by_cases htits : j=.tits
  · subst j
    exact PrimitiveSocleTitsCompleteOrdinary.genRank_le_ceiling D e hbelow
  by_cases hk : D.factorCount=1
  · cases j with
    | cyclic p hp =>
      exact (hnon (inferInstance : IsMulCommutative (Multiplicative (ZMod p)))).elim
    | alternating m hm => exact (hpair trivial).elim
    | A r q hr hs => exact (hpair trivial).elim
    | B r q hr => exact (hpair trivial).elim
    | C r q hr hs => exact (hpair trivial).elim
    | D r q hr => exact (hpair trivial).elim
    | suzuki m hm => exact (hpair trivial).elim
    | E6 q =>
      exact PrimitiveSocleExceptionalEOneFactorOrdinaryGenerators.typeE6_genRank_le_ceiling D hk q e
    | E7 q =>
      exact PrimitiveSocleExceptionalEOneFactorOrdinaryGenerators.typeE7_genRank_le_ceiling D hk q e
    | E8 q =>
      exact PrimitiveSocleExceptionalEOneFactorOrdinaryGenerators.typeE8_genRank_le_ceiling D hk q e
    | F4 q => exact PrimitiveSocleFFourAllDegreeOrdinary.genRank_le_ceiling D hk q e
    | G2 q hs => exact PrimitiveSocleGTwoAllDegreeOrdinary.genRank_le_ceiling D hk q hs e
    | twistedA r q hr hs =>
      exact PrimitiveSocleUnitaryCompleteOrdinary.genRank_le_ceiling D hk r q hr hs e
    | twistedD r q hr =>
      exact PrimitiveSocleTwistedDAllDegreeOrdinary.genRank_le_ceiling D hk r hr q e
    | twistedE6 q =>
      exact PrimitiveSocleTwistedE6OneFactorOrdinaryGenerators.genRank_le_ceiling D hk q e
    | trialityD4 q => exact PrimitiveSocleTrialityAllDegreeOrdinary.genRank_le_ceiling D hk q e
    | reeG2 m hm => exact PrimitiveSocleReeGTwoAllDegreeOrdinary.genRank_le_ceiling D hk m hm e
    | reeF4 m hm => exact PrimitiveSocleReeFFourAllDegreeOrdinary.genRank_le_ceiling D hk m hm e
    | tits => exact (htits rfl).elim
    | sporadic s =>
      by_cases hs : ¬CFSGGeneration.SporadicGenerationResidual s
      · exact SporadicPairAllDegreeOrdinary.primitive_genRank_le_ceiling remaining D s hs e hbelow
      by_cases hj4 : s=.j4
      · subst s
        exact PrimitiveSocleJFourCompleteOrdinary.genRank_le_ceiling remaining D hk e
      have hy : IsYSectionModel s := by
        by_contra hh
        cases s <;> simp_all [CFSGGeneration.SporadicGenerationResidual,IsYSectionModel]
      have h27 := PrimitiveSocleYSectionSmallActionExclusion.degree_ge_twentySeven D s hy e
      exact PrimitiveSocleYSectionOrdinaryFromSeventeen.genRank_le_ceiling
        remaining D hk s hy e (by omega)
  · obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
    have hp := sufficientSimpleIndexBounds_of_mulEquiv e (model_packet remaining j hnon) ell hell
    exact TraceyOrdinaryRetainedIndexResidual.multifactor_genRank_le_ceiling_of_actual_packet
      D ell hell (by have hpos := D.factorCount_pos; omega) hp.1 hp.2 hbelow

end SymmetricSubgroupAsymptotics.OldNonMonsterPrimitiveOrdinary
