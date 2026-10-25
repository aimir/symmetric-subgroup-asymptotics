import SymmetricSubgroupAsymptotics.TraceyOrdinarySevenModelResidual
import SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionOrdinaryFromThirtyTwo
import SymmetricSubgroupAsymptotics.OriginalNonaffineYAndTitsSmallBlockOrdinaryStep
import SymmetricSubgroupAsymptotics.PrimitiveSocleThirteenPointTitsExclusion

/-! A cumulative conditional refinement of the SAME actual ordinary
counterexample witness. The four Y heads pay primitive degrees>=32 and
original local degrees20..31; the original seven-generator Tits head
pays local degrees18..31. Its actual positive order divisor excludes
faithful degrees below14. Monster remains unrestricted. The numerical
callback is unchanged, explicit, and NOT discharged here. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TraceyOrdinaryBoundedHeadModelResidual
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions CFSGReduction
open TraceyOrdinarySporadicPairResidual (RemainingPairModel)

variable
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i)
    {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)]

/-- Every displayed factor/action is the original witness. The tag guards
are literal CFSG tags, not replacement socles or supplied rank budgets. -/
def ActualResidual : Prop :=
  (MulAction.IsPreprimitive J (Fin n) ∧
    ∃ D : NonaffineData J (Fin n), D.factorCount = 1 ∧
      ∃ i : CFSG.Index, RemainingPairModel i ∧ Nonempty (D.Simple ≃* i.Model) ∧
        i ≠ .sporadic .j4 ∧
        (∀ s, i = .sporadic s → PrimitiveSocleYSectionOrdinaryTail.IsYSectionModel s → n < 32) ∧
        (i = .tits → 14 ≤ n ∧ n < 128)) ∨
  (¬ MulAction.IsPreprimitive J (Fin n) ∧
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      ∃ D : NonaffineData block.Component block.Fibre, Nat.card block.Fibre < 32 ∧
        ∃ i : CFSG.Index, RemainingPairModel i ∧ Nonempty (D.Simple ≃* i.Model) ∧
          i ≠ .sporadic .j4 ∧
          (∀ s, i = .sporadic s → PrimitiveSocleYSectionOrdinaryTail.IsYSectionModel s →
            Nat.card block.Fibre < 20) ∧
          (i = .tits → 14 ≤ Nat.card block.Fibre ∧ Nat.card block.Fibre < 18))

include remaining in
theorem actual_residual_of_failed_coarse
    (hCFSG : CFSG.CFSGClassification) (hn : 2 ≤ n)
    (hbad : traceyPermutationGeneratorCeiling n < MarkedC4.genRank J)
    (hbelow : SmallerTransitiveRankBound n) : ActualResidual J := by
  have hr := TraceyOrdinarySevenModelResidual.actual_residual_of_failed_coarse
    remaining J hCFSG hn hbad hbelow
  rcases hr with ⟨hp,D,hk,i,hi,he,hnoj4,_h64,h128⟩ | ⟨hp,x₀,block,D,hlocal,i,hi,he,hnoj4⟩
  · have hY : ∀ s, i = .sporadic s → PrimitiveSocleYSectionOrdinaryTail.IsYSectionModel s →
        n < 32 := by
      intro s hj hs
      subst i
      by_contra hh
      obtain ⟨e⟩ := he
      have hpaid := PrimitiveSocleYSectionOrdinaryFromThirtyTwo.genRank_le_ceiling
        remaining D hk s hs e (by simpa only [Nat.card_fin] using (show 32 ≤ n by omega))
      exact not_lt_of_ge (by simpa only [Nat.card_fin] using hpaid) hbad
    have hT : i = .tits → 14 ≤ n ∧ n < 128 := by
      intro hj
      subst i
      obtain ⟨e⟩ := he
      have e0 : D.Simple ≃* CFSG.Models.Tits := by
        simpa only [CFSG.Index.instGroupModel,CFSG.Index.Model] using e
      constructor
      · by_contra hh
        exact PrimitiveSocleThirteenPointTitsExclusion.not_tits_of_degree_le_thirteen
          D (by simpa only [Nat.card_fin] using (show n ≤ 13 by omega)) e0
      · rcases h128 with h | h
        · exact h
        · cases h
    exact Or.inl ⟨hp,D,hk,i,hi,he,hnoj4,hY,hT⟩
  · letI : Fintype block.Points := Fintype.ofFinite _
    have hY : ∀ s, i = .sporadic s → PrimitiveSocleYSectionOrdinaryTail.IsYSectionModel s →
        Nat.card block.Fibre < 20 := by
      intro s hj hs
      subst i
      by_contra hh
      obtain ⟨e⟩ := he
      have hpaid := OriginalNonaffineYAndTitsSmallBlockOrdinaryStep.y_genRank_le_ceiling
        remaining J block D block.base (by omega) hlocal s hs e hbelow
      exact not_lt_of_ge hpaid hbad
    have hT : i = .tits → 14 ≤ Nat.card block.Fibre ∧ Nat.card block.Fibre < 18 := by
      intro hj
      subst i
      obtain ⟨e⟩ := he
      have e0 : D.Simple ≃* CFSG.Models.Tits := by
        simpa only [CFSG.Index.instGroupModel,CFSG.Index.Model] using e
      constructor
      · by_contra hh
        exact PrimitiveSocleThirteenPointTitsExclusion.not_tits_of_degree_le_thirteen
          D (by omega) e0
      · by_contra hh
        have hpaid := OriginalNonaffineYAndTitsSmallBlockOrdinaryStep.tits_genRank_le_ceiling
          remaining J block D block.base (by omega) hlocal e hbelow
        exact not_lt_of_ge hpaid hbad
    exact Or.inr ⟨hp,x₀,block,D,hlocal,i,hi,he,hnoj4,hY,hT⟩

include remaining in
theorem traceyPermutation_or_actual_minimal_bounded_head_model_residual
    (hCFSG : CFSG.CFSGClassification) :
    TraceyPermutationGeneratorInput ∨
      ∃ n : ℕ, 2 ≤ n ∧ ∃ J : Subgroup (Equiv.Perm (Fin n)),
        ∃ ht : MulAction.IsPretransitive J (Fin n),
          letI := ht
          traceyPermutationGeneratorCeiling n < MarkedC4.genRank J ∧
          SmallerTransitiveRankBound n ∧ ActualResidual J := by
  rcases TraceyOrdinarySevenModelResidual.traceyPermutation_or_actual_minimal_seven_model_residual
    remaining hCFSG with h | ⟨m,hm,L,ht,hbad,hbelow,_⟩
  · exact Or.inl h
  · letI := ht
    exact Or.inr ⟨m,hm,L,ht,hbad,hbelow,
      actual_residual_of_failed_coarse remaining L hCFSG hm hbad hbelow⟩

end SymmetricSubgroupAsymptotics.TraceyOrdinaryBoundedHeadModelResidual
