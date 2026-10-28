import SymmetricSubgroupAsymptotics.OldNonMonsterPrimitiveOrdinary
import SymmetricSubgroupAsymptotics.OriginalNonaffineOrdinaryLieCFSGReduction
import SymmetricSubgroupAsymptotics.OriginalNonaffineTitsCompleteOrdinaryStep
import SymmetricSubgroupAsymptotics.OriginalNonaffineJFourSmallBlockOrdinaryStep
import SymmetricSubgroupAsymptotics.OriginalNonaffineYAndTitsSmallBlockOrdinaryStep

/-! Per-model original-block frontend, with no old classification input.
The selected component, simple factor, map, fibre and actual top are unchanged.
Only the already retained simple-index callback is consumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OldNonMonsterOriginalOrdinaryStep
open PrimitiveSocleRawStructure CFSGReduction TraceyStrictlySmallerTransitiveActions
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)
open PrimitiveSocleYSectionOrdinaryTail (IsYSectionModel)

private theorem isY_of_residual (s : CFSG.Sporadic)
    (hs : CFSGGeneration.SporadicGenerationResidual s) (hj4 : s≠.j4)
    (hm : s≠.monster) : IsYSectionModel s := by
  cases s <;> simp_all only [CFSGGeneration.SporadicGenerationResidual,IsYSectionModel]
  case j4 => exact hj4 rfl
  case monster => exact hm rfl

variable (remaining : ∀ (j : CFSG.Index) [Finite j.Model] [IsSimpleGroup j.Model],
    ¬IsMulCommutative j.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter j →
      ModelBoundsAfterReeFFourIndexSquare j)
    {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (D : NonaffineData block.Component block.Fibre)

include remaining in
theorem genRank_le_ceiling (j : CFSG.Index) (hnot : j≠.sporadic .monster)
    (e : D.Simple ≃* j.Model) (i : block.Points) (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  letI : Finite j.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup j.Model := e.symm.isSimpleGroup
  have hnon : ¬IsMulCommutative j.Model :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  by_cases htits : j=.tits
  · subst j
    exact OriginalNonaffineTitsCompleteOrdinaryStep.genRank_le_ceiling J block D i e hbelow
  by_cases h32 : 32 ≤ Nat.card block.Fibre
  · obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
    obtain ⟨horder,houter⟩ := sufficientSimpleIndexBounds_of_mulEquiv e
      (OldNonMonsterPrimitiveOrdinary.model_packet remaining j hnon) ell hell
    exact OriginalNonaffineThirtyTwoOrdinaryStep.genRank_le_ceiling_of_actual_packet
      J block D i h32 hbelow ell hell horder houter
  have hsmall : Nat.card block.Fibre < 32 := by omega
  by_cases hpair : PairFamily j
  · exact OriginalNonaffinePairFamiliesAllDegreeOrdinaryStep.genRank_le_ceiling
      J block D j hpair e i hbelow
  cases j with
  | cyclic p hp =>
    exact (hnon (inferInstance : IsMulCommutative (Multiplicative (ZMod p)))).elim
  | alternating m hm => exact (hpair trivial).elim
  | A r q hr hs => exact (hpair trivial).elim
  | B r q hr => exact (hpair trivial).elim
  | C r q hr hs => exact (hpair trivial).elim
  | D r q hr => exact (hpair trivial).elim
  | suzuki m hm => exact (hpair trivial).elim
  | twistedA r q hr hs =>
    exact OriginalNonaffineUnitaryBlockOrdinaryStep.genRank_le_ceiling
      J block D r q hr hs e i hbelow
  | twistedD r q hr =>
    exact OriginalNonaffineTwistedDBlockOrdinaryStep.genRank_le_ceiling
      J block D r hr q e i hbelow
  | E6 q =>
    letI : IsSimpleGroup (CFSG.Models.E6 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeESix q)
    omega
  | E7 q =>
    letI : IsSimpleGroup (CFSG.Models.E7 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeESeven q)
    omega
  | E8 q =>
    letI : IsSimpleGroup (CFSG.Models.E8 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeEEight q)
    omega
  | F4 q =>
    letI : IsSimpleGroup (CFSG.Models.F4 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeFFour q)
    omega
  | G2 q hs =>
    letI : IsSimpleGroup (CFSG.Models.G2 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeGTwo q hs)
    omega
  | twistedE6 q =>
    letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeTwistedESix q)
    omega
  | trialityD4 q =>
    letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeTriality q)
    omega
  | reeG2 m hm =>
    letI : IsSimpleGroup (CFSG.Models.ReeG2 m) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeReeGTwo m hm)
    omega
  | reeF4 m hm =>
    letI : IsSimpleGroup (CFSG.Models.ReeF4 m) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeReeFFour m hm)
    omega
  | tits => exact (htits rfl).elim
  | sporadic s =>
    by_cases hs : ¬CFSGGeneration.SporadicGenerationResidual s
    · exact SporadicPairAllDegreeOrdinary.original_block_genRank_le_ceiling
        remaining J block D s hs e i hbelow
    by_cases hj4 : s=.j4
    · subst s
      exact OriginalNonaffineJFourSmallBlockOrdinaryStep.genRank_le_ceiling
        remaining J block D i hsmall e hbelow
    have hm : s≠.monster := fun hh => hnot (congrArg CFSG.Index.sporadic hh)
    have hy : IsYSectionModel s := isY_of_residual s (not_not.mp hs) hj4 hm
    have h27 := PrimitiveSocleYSectionSmallActionExclusion.degree_ge_twentySeven D s hy e
    exact OriginalNonaffineYAndTitsSmallBlockOrdinaryStep.y_genRank_le_ceiling
      remaining J block D i (by omega) hsmall s hy e hbelow

end SymmetricSubgroupAsymptotics.OldNonMonsterOriginalOrdinaryStep
