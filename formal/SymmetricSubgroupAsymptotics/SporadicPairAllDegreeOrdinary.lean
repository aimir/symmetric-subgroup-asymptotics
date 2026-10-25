import SymmetricSubgroupAsymptotics.TraceyOrdinarySporadicPairResidual
import SymmetricSubgroupAsymptotics.PrimitiveSocleSufficientPairAllDegreeOrdinary
import SymmetricSubgroupAsymptotics.OriginalNonaffineTinyPairBlockOrdinaryStep

/-! The actual displayed pairs of twenty sporadic models pay EVERY
primitive degree and EVERY original nonaffine block degree/top, by the
already checked generic pair installers. The same retained numerical
callback supplies the actual model packet; no new generator premise or
large-degree cutoff remains for these twenty models. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SporadicPairAllDegreeOrdinary
open PrimitiveSocleRawStructure CFSGReduction TraceyStrictlySmallerTransitiveActions

variable
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i)

include remaining in
theorem model_packet (s : CFSG.Sporadic)
    [Finite (CFSG.Index.sporadic s).Model] [IsSimpleGroup (CFSG.Index.sporadic s).Model]
    (hn : ¬ IsMulCommutative (CFSG.Index.sporadic s).Model) :
    ModelSufficientSimpleIndexBounds (.sporadic s) := remaining (.sporadic s) hn (by trivial)

include remaining in
theorem primitive_genRank_le_ceiling
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X) (s : CFSG.Sporadic)
    (hs : ¬ CFSGGeneration.SporadicGenerationResidual s)
    (e : D.Simple ≃* (CFSG.Index.sporadic s).Model)
    (hbelow : SmallerTransitiveRankBound (Nat.card X)) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : Finite (CFSG.Index.sporadic s).Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup (CFSG.Index.sporadic s).Model := e.symm.isSimpleGroup
  have hni : ¬ IsMulCommutative (CFSG.Index.sporadic s).Model := by
    intro hc
    exact D.noncommutative ((isMulCommutative_congr e).mpr hc)
  have hp := model_packet remaining s hni
  have hpair : CFSGGeneration.TwoGenerated (CFSG.Index.sporadic s).Model :=
    CFSGGeneration.sporadic_twoGenerated_of_not_residual s hs
  by_cases hk : D.factorCount = 1
  · exact PrimitiveSocleSufficientPairAllDegreeOrdinary.genRank_le_ceiling
      D hk e hpair (fun ell hell => (hp ell hell).2)
  · obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
    have hactual := sufficientSimpleIndexBounds_of_mulEquiv e hp ell hell
    have hsimple : MarkedC4.genRank D.Simple ≤ 2 := by
      rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
      obtain ⟨S,hS,hcard⟩ := hpair
      exact (MarkedC4.genRank_le hS).trans hcard
    exact PrimitiveSocleBoundedMultiplePairOrdinary.genRank_le_ceiling D ell hbelow hell
      (by have hpos := D.factorCount_pos; omega) hactual.1 hactual.2 hsimple

include remaining in
theorem original_block_genRank_le_ceiling
    {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (D : NonaffineData block.Component block.Fibre)
    (s : CFSG.Sporadic) (hs : ¬ CFSGGeneration.SporadicGenerationResidual s)
    (e : D.Simple ≃* (CFSG.Index.sporadic s).Model)
    (i : block.Points) (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  letI : Finite (CFSG.Index.sporadic s).Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup (CFSG.Index.sporadic s).Model := e.symm.isSimpleGroup
  have hni : ¬ IsMulCommutative (CFSG.Index.sporadic s).Model := by
    intro hc
    exact D.noncommutative ((isMulCommutative_congr e).mpr hc)
  have hp := model_packet remaining s hni
  have hpair : CFSGGeneration.TwoGenerated (CFSG.Index.sporadic s).Model :=
    CFSGGeneration.sporadic_twoGenerated_of_not_residual s hs
  exact OriginalNonaffineTinyPairBlockOrdinaryStep.genRank_le_ceiling_of_model
    J block D e hpair hp i hbelow

end SymmetricSubgroupAsymptotics.SporadicPairAllDegreeOrdinary
