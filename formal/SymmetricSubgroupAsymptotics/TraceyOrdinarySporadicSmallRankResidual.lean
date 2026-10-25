import SymmetricSubgroupAsymptotics.TraceyOrdinarySporadicPairResidual
import SymmetricSubgroupAsymptotics.CFSGJ4Generation
import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorTripleOrdinaryTail

/-! The actual three-generator J4 presentation also pays the original
primitive coarse ordinary bound from degree32. Together with the twenty
proved sporadic pairs, only Tits and five sporadic tags remain above32.
Small original actions and block fibres remain explicit, and the same
retained numerical callback is used throughout. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TraceyOrdinarySporadicSmallRankResidual
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction CFSGReduction

variable
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i)

include remaining in
theorem j4_genRank_le_ceiling
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hk : D.factorCount = 1)
    (e : D.Simple ≃* (CFSG.Index.sporadic .j4).Model) (hn : 32 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : Finite (CFSG.Index.sporadic .j4).Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup (CFSG.Index.sporadic .j4).Model := e.symm.isSimpleGroup
  have hni : ¬ IsMulCommutative (CFSG.Index.sporadic .j4).Model := by
    intro hc
    exact D.noncommutative ((isMulCommutative_congr e).mpr hc)
  have hp : ModelSufficientSimpleIndexBounds (.sporadic .j4) :=
    remaining (.sporadic .j4) hni (by trivial)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hout := (sufficientSimpleIndexBounds_of_mulEquiv e hp ell hell).2
  have hsimple : MarkedC4.genRank D.Simple ≤ 3 := by
    let e0 : D.Simple ≃* CFSG.Models.Presentations.J4.Model := e
    letI : Finite CFSG.Models.Presentations.J4.Model := Finite.of_equiv D.Simple e0.toEquiv
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e0]
    obtain ⟨S,hS,hcard⟩ := CFSGGeneration.j4_three_generators
    exact (MarkedC4.genRank_le hS).trans hcard
  exact PrimitiveSocleOneFactorTripleOrdinaryTail.genRank_le_ceiling
    D hk hsimple ell hell hout hn

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)]

def ActualResidual : Prop :=
  (MulAction.IsPreprimitive J (Fin n) ∧
    ∃ D : NonaffineData J (Fin n), D.factorCount = 1 ∧
      ∃ i : CFSG.Index, RemainingModel i ∧ Nonempty (D.Simple ≃* i.Model) ∧
        (n < 32 ∨ (TraceyOrdinarySporadicPairResidual.RemainingPairModel i ∧
          i ≠ .sporadic .j4))) ∨
  (¬ MulAction.IsPreprimitive J (Fin n) ∧
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      ∃ D : NonaffineData block.Component block.Fibre, Nat.card block.Fibre < 32 ∧
        ∃ i : CFSG.Index, RemainingModel i ∧ Nonempty (D.Simple ≃* i.Model))

include remaining in
theorem actual_residual_of_failed_coarse
    (hCFSG : CFSG.CFSGClassification) (hn : 2 ≤ n)
    (hbad : traceyPermutationGeneratorCeiling n < MarkedC4.genRank J)
    (hbelow : SmallerTransitiveRankBound n) : ActualResidual J := by
  have hr := TraceyOrdinarySporadicPairResidual.actual_residual_of_failed_coarse
    remaining J hCFSG hn hbad hbelow
  rcases hr with ⟨hp,D,hk,i,hi,he,hm⟩ | hr
  · left
    refine ⟨hp,D,hk,i,hi,he,?_⟩
    rcases hm with hsmall | hpair
    · exact Or.inl hsmall
    · by_cases hsmall : n < 32
      · exact Or.inl hsmall
      · refine Or.inr ⟨hpair,?_⟩
        intro hij4
        subst i
        obtain ⟨e⟩ := he
        have hh := j4_genRank_le_ceiling remaining D hk e
          (by simpa only [Nat.card_fin] using (show 32 ≤ n by omega))
        exact not_lt_of_ge (by simpa only [Nat.card_fin] using hh) hbad
  · exact Or.inr hr

include remaining in
theorem traceyPermutation_or_actual_minimal_small_rank_residual
    (hCFSG : CFSG.CFSGClassification) :
    TraceyPermutationGeneratorInput ∨
      ∃ n : ℕ, 2 ≤ n ∧ ∃ J : Subgroup (Equiv.Perm (Fin n)),
        ∃ ht : MulAction.IsPretransitive J (Fin n),
          letI := ht
          traceyPermutationGeneratorCeiling n < MarkedC4.genRank J ∧
          SmallerTransitiveRankBound n ∧ ActualResidual J := by
  rcases TraceyOrdinarySporadicPairResidual.traceyPermutation_or_actual_minimal_pair_residual
    remaining hCFSG with h | ⟨m,hm,L,ht,hbad,hbelow,_⟩
  · exact Or.inl h
  · letI := ht
    exact Or.inr ⟨m,hm,L,ht,hbad,hbelow,
      actual_residual_of_failed_coarse remaining L hCFSG hm hbad hbelow⟩

end SymmetricSubgroupAsymptotics.TraceyOrdinarySporadicSmallRankResidual
