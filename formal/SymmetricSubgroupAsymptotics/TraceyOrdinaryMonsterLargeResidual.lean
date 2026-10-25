import SymmetricSubgroupAsymptotics.PrimitiveSocleTitsOrderOrdinaryTail

/-! Above degree127 the primitive coarse ordinary counterexample retains
only the actual Monster simple model. Below that threshold and in small
local blocks the previous precise data remain. The unchanged numerical
callback is used, not a new generation or finite-coverage assumption. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TraceyOrdinaryMonsterLargeResidual
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction CFSGReduction

variable
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i)
    {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)]

def ActualResidual : Prop :=
  (n < 128 ∧ TraceyOrdinaryTitsMonsterResidual.ActualResidual J) ∨
  (MulAction.IsPreprimitive J (Fin n) ∧
    ∃ D : NonaffineData J (Fin n), D.factorCount = 1 ∧
      Nonempty (D.Simple ≃* (CFSG.Index.sporadic .monster).Model)) ∨
  (¬ MulAction.IsPreprimitive J (Fin n) ∧
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      ∃ D : NonaffineData block.Component block.Fibre, Nat.card block.Fibre < 32 ∧
        ∃ i : CFSG.Index, RemainingModel i ∧ Nonempty (D.Simple ≃* i.Model))

include remaining in
theorem actual_residual_of_failed_coarse
    (hCFSG : CFSG.CFSGClassification) (hn : 2 ≤ n)
    (hbad : traceyPermutationGeneratorCeiling n < MarkedC4.genRank J)
    (hbelow : SmallerTransitiveRankBound n) : ActualResidual J := by
  have hr := TraceyOrdinaryTitsMonsterResidual.actual_residual_of_failed_coarse
    remaining J hCFSG hn hbad hbelow
  by_cases hsmall : n < 128
  · exact Or.inl ⟨hsmall,hr⟩
  · right
    rcases hr with ⟨hp,D,hk,i,hi,he,_,hm⟩ | hr
    · left
      have htag : i = .tits ∨ i = .sporadic .monster := hm.resolve_left (by omega)
      rcases htag with rfl | rfl
      · obtain ⟨e⟩ := he
        have hh := PrimitiveSocleTitsOrderOrdinaryTail.genRank_le_ceiling D remaining hk e
          (by simpa only [Nat.card_fin] using (show 128 ≤ n by omega))
        exact (not_lt_of_ge (by simpa only [Nat.card_fin] using hh) hbad).elim
      · exact ⟨hp,D,hk,he⟩
    · exact Or.inr hr

include remaining in
theorem traceyPermutation_or_actual_minimal_monster_large_residual
    (hCFSG : CFSG.CFSGClassification) :
    TraceyPermutationGeneratorInput ∨
      ∃ n : ℕ, 2 ≤ n ∧ ∃ J : Subgroup (Equiv.Perm (Fin n)),
        ∃ ht : MulAction.IsPretransitive J (Fin n),
          letI := ht
          traceyPermutationGeneratorCeiling n < MarkedC4.genRank J ∧
          SmallerTransitiveRankBound n ∧ ActualResidual J := by
  rcases TraceyOrdinaryTitsMonsterResidual.traceyPermutation_or_actual_minimal_tits_monster_residual
    remaining hCFSG with h | ⟨m,hm,L,ht,hbad,hbelow,_⟩
  · exact Or.inl h
  · letI := ht
    exact Or.inr ⟨m,hm,L,ht,hbad,hbelow,
      actual_residual_of_failed_coarse remaining L hCFSG hm hbad hbelow⟩

end SymmetricSubgroupAsymptotics.TraceyOrdinaryMonsterLargeResidual
