import SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionOrdinaryTail

/-! With the numerical callback already retained by T1, an actual least
coarse ordinary counterexample above degree63 has only Tits or Monster
as its primitive simple factor. The exact original smaller-action and
small-block alternatives are retained. No new model/rank premise is
introduced and no finite-model obligation is assumed proved. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TraceyOrdinaryTitsMonsterResidual
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction CFSGReduction

private theorem y_section_of_remaining (i : CFSG.Index)
    (hp : TraceyOrdinarySporadicPairResidual.RemainingPairModel i)
    (hJ4 : i ≠ .sporadic .j4) (hT : i ≠ .tits) (hM : i ≠ .sporadic .monster) :
    ∃ s, i = .sporadic s ∧ PrimitiveSocleYSectionOrdinaryTail.IsYSectionModel s := by
  cases i <;> try { exact False.elim hp }
  case tits => exact (hT rfl).elim
  case sporadic s =>
    cases s <;> simp_all [TraceyOrdinarySporadicPairResidual.RemainingPairModel,
      CFSGGeneration.SporadicGenerationResidual,PrimitiveSocleYSectionOrdinaryTail.IsYSectionModel]

variable
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i)
    {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)]

def ActualResidual : Prop :=
  (MulAction.IsPreprimitive J (Fin n) ∧
    ∃ D : NonaffineData J (Fin n), D.factorCount = 1 ∧
      ∃ i : CFSG.Index, RemainingModel i ∧ Nonempty (D.Simple ≃* i.Model) ∧
        (n < 32 ∨ (TraceyOrdinarySporadicPairResidual.RemainingPairModel i ∧
          i ≠ .sporadic .j4)) ∧
        (n < 64 ∨ i = .tits ∨ i = .sporadic .monster)) ∨
  (¬ MulAction.IsPreprimitive J (Fin n) ∧
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      ∃ D : NonaffineData block.Component block.Fibre, Nat.card block.Fibre < 32 ∧
        ∃ i : CFSG.Index, RemainingModel i ∧ Nonempty (D.Simple ≃* i.Model))

include remaining in
theorem actual_residual_of_failed_coarse
    (hCFSG : CFSG.CFSGClassification) (hn : 2 ≤ n)
    (hbad : traceyPermutationGeneratorCeiling n < MarkedC4.genRank J)
    (hbelow : SmallerTransitiveRankBound n) : ActualResidual J := by
  have hr := TraceyOrdinarySporadicSmallRankResidual.actual_residual_of_failed_coarse
    remaining J hCFSG hn hbad hbelow
  rcases hr with ⟨hp,D,hk,i,hi,he,hm⟩ | hr
  · left
    refine ⟨hp,D,hk,i,hi,he,hm,?_⟩
    by_cases hsmall : n < 64
    · exact Or.inl hsmall
    · right
      by_cases hT : i = .tits
      · exact Or.inl hT
      · by_cases hM : i = .sporadic .monster
        · exact Or.inr hM
        · have hm1 : TraceyOrdinarySporadicPairResidual.RemainingPairModel i ∧
              i ≠ .sporadic .j4 := hm.resolve_left (by omega)
          obtain ⟨s,rfl,hs⟩ := y_section_of_remaining i hm1.1 hm1.2 hT hM
          obtain ⟨e⟩ := he
          have hh := PrimitiveSocleYSectionOrdinaryTail.genRank_le_ceiling remaining D hk s hs e
            (by simpa only [Nat.card_fin] using (show 64 ≤ n by omega))
          exact (not_lt_of_ge (by simpa only [Nat.card_fin] using hh) hbad).elim
  · exact Or.inr hr

include remaining in
theorem traceyPermutation_or_actual_minimal_tits_monster_residual
    (hCFSG : CFSG.CFSGClassification) :
    TraceyPermutationGeneratorInput ∨
      ∃ n : ℕ, 2 ≤ n ∧ ∃ J : Subgroup (Equiv.Perm (Fin n)),
        ∃ ht : MulAction.IsPretransitive J (Fin n),
          letI := ht
          traceyPermutationGeneratorCeiling n < MarkedC4.genRank J ∧
          SmallerTransitiveRankBound n ∧ ActualResidual J := by
  rcases TraceyOrdinarySporadicSmallRankResidual.traceyPermutation_or_actual_minimal_small_rank_residual
    remaining hCFSG with h | ⟨m,hm,L,ht,hbad,hbelow,_⟩
  · exact Or.inl h
  · letI := ht
    exact Or.inr ⟨m,hm,L,ht,hbad,hbelow,
      actual_residual_of_failed_coarse remaining L hCFSG hm hbad hbelow⟩

end SymmetricSubgroupAsymptotics.TraceyOrdinaryTitsMonsterResidual
