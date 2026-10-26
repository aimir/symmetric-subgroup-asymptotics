import SymmetricSubgroupAsymptotics.TraceyOrdinaryBoundedHeadModelResidual
import SymmetricSubgroupAsymptotics.PrimitiveSocleTitsCompleteOrdinary
import SymmetricSubgroupAsymptotics.OriginalNonaffineTitsCompleteOrdinaryStep
import SymmetricSubgroupAsymptotics.CFSGSevenTargetsTitsComplete

/-! Actual Tits ordinary bounds remove that model from the coarse
transitive residual. Only Fi22, Fi24′, Baby and Monster survive, on the SAME primitive socle or original block
component. The sporadic numerical callback is explicit; this is not a
proof of the entire coarse theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TraceyOrdinaryFourSporadicResidual
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions CFSGReduction
open TraceyOrdinarySporadicPairResidual (RemainingPairModel)

variable
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterTits i →
        ModelBoundsAfterTitsIndexSquare i)

include remaining in
private theorem full_callback (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬ IsMulCommutative i.Model)
    (hi : RemainingSufficientSimpleIndexAfterReeFFourOuter i) :
    ModelBoundsAfterReeFFourIndexSquare i :=
  modelBoundsAfterReeFFourSquare_of_after_Tits_square i hn
    (simpleIndex_callback_after_Tits remaining i hn hi)

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)]

def ActualResidual : Prop :=
  (MulAction.IsPreprimitive J (Fin n) ∧
    ∃ D : NonaffineData J (Fin n), D.factorCount = 1 ∧
      ∃ s : CFSG.Sporadic, CFSGGeneration.SporadicGenerationResidual s ∧
        Nonempty (D.Simple ≃* s.Model) ∧ s ≠ .j4 ∧ s ≠ .fi23 ∧
        (PrimitiveSocleYSectionOrdinaryTail.IsYSectionModel s → n < 12)) ∨
  (¬ MulAction.IsPreprimitive J (Fin n) ∧
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      ∃ D : NonaffineData block.Component block.Fibre, Nat.card block.Fibre < 32 ∧
        ∃ s : CFSG.Sporadic, CFSGGeneration.SporadicGenerationResidual s ∧
          Nonempty (D.Simple ≃* s.Model) ∧ s ≠ .j4 ∧ s ≠ .fi23 ∧
          (PrimitiveSocleYSectionOrdinaryTail.IsYSectionModel s → Nat.card block.Fibre < 18))

include remaining in
theorem actual_residual_of_failed_coarse
    (hCFSG : CFSG.CFSGClassification) (hn : 2 ≤ n)
    (hbad : traceyPermutationGeneratorCeiling n < MarkedC4.genRank J)
    (hbelow : SmallerTransitiveRankBound n) : ActualResidual J := by
  have hr := TraceyOrdinaryBoundedHeadModelResidual.actual_residual_of_failed_coarse
    (full_callback remaining) J hCFSG hn hbad hbelow
  rcases hr with ⟨hp,D,hk,i,hi,he,hnoj4,hno23,hY,_⟩ |
    ⟨hp,x₀,block,D,hlocal,i,hi,he,hnoj4,hno23,hY,_⟩
  · letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
      (by simpa only [Nat.card_fin] using (show 1 < n by omega))
    letI : MulAction.IsPreprimitive J (Fin n) := hp
    have hnotits : i ≠ .tits := by
      intro ht
      subst i
      obtain ⟨e⟩ := he
      have hbound := PrimitiveSocleTitsCompleteOrdinary.genRank_le_ceiling D e
        (by simpa only [Nat.card_fin] using hbelow)
      exact not_lt_of_ge (by simpa only [Nat.card_fin] using hbound) hbad
    have hsporadic : ∃ s, i = .sporadic s := by
      cases i <;> try exact False.elim hi
      case tits => exact (hnotits rfl).elim
      case sporadic => exact ⟨_,rfl⟩
    obtain ⟨s,rfl⟩ := hsporadic
    refine Or.inl ⟨hp,D,hk,s,hi,he,?_,?_,?_⟩
    · intro hs
      exact hnoj4 (congrArg CFSG.Index.sporadic hs)
    · intro hs
      exact hno23 (congrArg CFSG.Index.sporadic hs)
    · exact hY s rfl
  · letI : Fintype block.Points := Fintype.ofFinite _
    have hnotits : i ≠ .tits := by
      intro ht
      subst i
      obtain ⟨e⟩ := he
      have hbound := OriginalNonaffineTitsCompleteOrdinaryStep.genRank_le_ceiling
        J block D block.base e hbelow
      exact not_lt_of_ge hbound hbad
    have hsporadic : ∃ s, i = .sporadic s := by
      cases i <;> try exact False.elim hi
      case tits => exact (hnotits rfl).elim
      case sporadic => exact ⟨_,rfl⟩
    obtain ⟨s,rfl⟩ := hsporadic
    refine Or.inr ⟨hp,x₀,block,D,hlocal,s,hi,he,?_,?_,?_⟩
    · intro hs
      exact hnoj4 (congrArg CFSG.Index.sporadic hs)
    · intro hs
      exact hno23 (congrArg CFSG.Index.sporadic hs)
    · exact hY s rfl

include remaining in
theorem traceyPermutation_or_actual_minimal_four_sporadic_residual
    (hCFSG : CFSG.CFSGClassification) :
    TraceyPermutationGeneratorInput ∨
      ∃ n : ℕ, 2 ≤ n ∧ ∃ J : Subgroup (Equiv.Perm (Fin n)),
        ∃ ht : MulAction.IsPretransitive J (Fin n),
          letI := ht
          traceyPermutationGeneratorCeiling n < MarkedC4.genRank J ∧
          SmallerTransitiveRankBound n ∧ ActualResidual J := by
  rcases TraceyOrdinaryBoundedHeadModelResidual.traceyPermutation_or_actual_minimal_bounded_head_model_residual
    (full_callback remaining) hCFSG with h | ⟨m,hm,L,ht,hbad,hbelow,_⟩
  · exact Or.inl h
  · letI := ht
    exact Or.inr ⟨m,hm,L,ht,hbad,hbelow,
      actual_residual_of_failed_coarse remaining L hCFSG hm hbad hbelow⟩

end SymmetricSubgroupAsymptotics.TraceyOrdinaryFourSporadicResidual
