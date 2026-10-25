import SymmetricSubgroupAsymptotics.TraceyOrdinaryMonsterLargeResidual
import SymmetricSubgroupAsymptotics.SporadicPairAllDegreeOrdinary

/-! The twenty displayed sporadic pairs are removed at every actual degree,
including every original small block fibre. Only Tits and the six models
without displayed pairs survive. Their primitive cutoffs are retained on
exactly the same socle witness: J4 below32, the four Y-section models below64,
Tits below128, and Monster unrestricted. The numerical callback already
present in the CFSG facade is unchanged; this is a reduction, not its discharge. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TraceyOrdinarySevenModelResidual
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction CFSGReduction
open TraceyOrdinarySporadicPairResidual (RemainingPairModel)

variable
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i)
    {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)]

def ActualResidual : Prop :=
  (MulAction.IsPreprimitive J (Fin n) ∧
    ∃ D : NonaffineData J (Fin n), D.factorCount = 1 ∧
      ∃ i : CFSG.Index, RemainingPairModel i ∧ Nonempty (D.Simple ≃* i.Model) ∧
        (n < 32 ∨ i ≠ .sporadic .j4) ∧
        (n < 64 ∨ i = .tits ∨ i = .sporadic .monster) ∧
        (n < 128 ∨ i = .sporadic .monster)) ∨
  (¬ MulAction.IsPreprimitive J (Fin n) ∧
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      ∃ D : NonaffineData block.Component block.Fibre, Nat.card block.Fibre < 32 ∧
        ∃ i : CFSG.Index, RemainingPairModel i ∧ Nonempty (D.Simple ≃* i.Model))

include remaining in
theorem actual_residual_of_failed_coarse
    (hCFSG : CFSG.CFSGClassification) (hn : 2 ≤ n)
    (hbad : traceyPermutationGeneratorCeiling n < MarkedC4.genRank J)
    (hbelow : SmallerTransitiveRankBound n) : ActualResidual J := by
  have hr := TraceyOrdinaryTitsMonsterResidual.actual_residual_of_failed_coarse
    remaining J hCFSG hn hbad hbelow
  rcases hr with ⟨hp,D,hk,i,hi,he,h32,h64⟩ | ⟨hp,x₀,block,D,hlocal,i,hi,he⟩
  · letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
      (by simpa only [Nat.card_fin] using (show 1 < n by omega))
    letI : MulAction.IsPreprimitive J (Fin n) := hp
    have hpair : RemainingPairModel i := by
      cases i <;> try { exact False.elim hi }
      case tits => trivial
      case sporadic s =>
        by_contra hs
        obtain ⟨e⟩ := he
        have hbound := SporadicPairAllDegreeOrdinary.primitive_genRank_le_ceiling
          remaining D s hs e (by simpa only [Nat.card_fin] using hbelow)
        exact not_lt_of_ge (by simpa only [Nat.card_fin] using hbound) hbad
    have h128 : n < 128 ∨ i = .sporadic .monster := by
      by_cases hsmall : n < 128
      · exact Or.inl hsmall
      · rcases h64.resolve_left (by omega) with ht | hm
        · subst i
          obtain ⟨e⟩ := he
          have hbound := PrimitiveSocleTitsOrderOrdinaryTail.genRank_le_ceiling
            D remaining hk e (by simpa only [Nat.card_fin] using (show 128 ≤ n by omega))
          exact (not_lt_of_ge (by simpa only [Nat.card_fin] using hbound) hbad).elim
        · exact Or.inr hm
    exact Or.inl ⟨hp,D,hk,i,hpair,he,h32.imp_right And.right,h64,h128⟩
  · letI : Fintype block.Points := Fintype.ofFinite _
    have hpair : RemainingPairModel i := by
      cases i <;> try { exact False.elim hi }
      case tits => trivial
      case sporadic s =>
        by_contra hs
        obtain ⟨e⟩ := he
        have hbound := SporadicPairAllDegreeOrdinary.original_block_genRank_le_ceiling
          remaining J block D s hs e block.base hbelow
        exact not_lt_of_ge hbound hbad
    exact Or.inr ⟨hp,x₀,block,D,hlocal,i,hpair,he⟩

include remaining in
theorem traceyPermutation_or_actual_minimal_seven_model_residual
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

end SymmetricSubgroupAsymptotics.TraceyOrdinarySevenModelResidual
