import SymmetricSubgroupAsymptotics.TraceyOrdinaryRetainedIndexResidual
import SymmetricSubgroupAsymptotics.CFSGSporadicGeneration
import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorPairOrdinaryTail

/-! The literal generating pairs of twenty pinned sporadic models pay
the actual one-factor coarse ordinary bound at every degree at least32.
Only the numerical callback already retained by the ReeF4-outer facade
is used. The six models without such a pair, Tits, and small actual
local actions remain explicit; no universal two-generation is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TraceyOrdinarySporadicPairResidual
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction CFSGReduction

variable
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i)

include remaining in
theorem sporadic_pair_genRank_le_ceiling
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hk : D.factorCount = 1)
    (s : CFSG.Sporadic) (hs : ¬ CFSGGeneration.SporadicGenerationResidual s)
    (e : D.Simple ≃* s.Model) (hn : 32 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : Finite s.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup s.Model := e.symm.isSimpleGroup
  let ei : D.Simple ≃* (CFSG.Index.sporadic s).Model := e
  letI : Finite (CFSG.Index.sporadic s).Model := Finite.of_equiv D.Simple ei.toEquiv
  letI : IsSimpleGroup (CFSG.Index.sporadic s).Model := ei.symm.isSimpleGroup
  have hni : ¬ IsMulCommutative s.Model := by
    intro hc
    exact D.noncommutative ((isMulCommutative_congr e).mpr hc)
  have hpacket : ModelSufficientSimpleIndexBounds (.sporadic s) :=
    remaining (.sporadic s) hni (by trivial)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hout := (sufficientSimpleIndexBounds_of_mulEquiv e hpacket ell hell).2
  obtain ⟨S,hS,hcard⟩ := CFSGGeneration.twoGenerated_of_mulEquiv_sporadic s hs e
  exact PrimitiveSocleOneFactorPairOrdinaryTail.genRank_le_ceiling D hk
    S hS hcard ell hell hout hn

def RemainingPairModel : CFSG.Index → Prop
  | .tits => True
  | .sporadic s => CFSGGeneration.SporadicGenerationResidual s
  | _ => False

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)]

def ActualResidual : Prop :=
  (MulAction.IsPreprimitive J (Fin n) ∧
    ∃ D : NonaffineData J (Fin n), D.factorCount = 1 ∧
      ∃ i : CFSG.Index, RemainingModel i ∧ Nonempty (D.Simple ≃* i.Model) ∧
        (n < 32 ∨ RemainingPairModel i)) ∨
  (¬ MulAction.IsPreprimitive J (Fin n) ∧
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      ∃ D : NonaffineData block.Component block.Fibre, Nat.card block.Fibre < 32 ∧
        ∃ i : CFSG.Index, RemainingModel i ∧ Nonempty (D.Simple ≃* i.Model))

include remaining in
theorem actual_residual_of_failed_coarse
    (hCFSG : CFSG.CFSGClassification) (hn : 2 ≤ n)
    (hbad : traceyPermutationGeneratorCeiling n < MarkedC4.genRank J)
    (hbelow : SmallerTransitiveRankBound n) : ActualResidual J := by
  have hr := TraceyOrdinaryRetainedIndexResidual.narrow_residual_of_failed_coarse
    J hCFSG remaining hn hbad hbelow
  rcases hr with ⟨hp,D,hk,i,hi,he⟩ | hr
  · left
    refine ⟨hp,D,hk,i,hi,he,?_⟩
    by_cases hsmall : n < 32
    · exact Or.inl hsmall
    · right
      have hitag : i = .tits ∨ ∃ s, i = .sporadic s := by
        cases i <;> simp_all [RemainingModel]
      rcases hitag with rfl | ⟨s,rfl⟩
      · trivial
      ·
        change CFSGGeneration.SporadicGenerationResidual s
        by_contra hs
        obtain ⟨e⟩ := he
        have hh := sporadic_pair_genRank_le_ceiling remaining D hk s hs e
          (by simpa only [Nat.card_fin] using (show 32 ≤ n by omega))
        exact not_lt_of_ge (by simpa only [Nat.card_fin] using hh) hbad
  · exact Or.inr hr

include remaining in
theorem traceyPermutation_or_actual_minimal_pair_residual
    (hCFSG : CFSG.CFSGClassification) :
    TraceyPermutationGeneratorInput ∨
      ∃ n : ℕ, 2 ≤ n ∧ ∃ J : Subgroup (Equiv.Perm (Fin n)),
        ∃ ht : MulAction.IsPretransitive J (Fin n),
          letI := ht
          traceyPermutationGeneratorCeiling n < MarkedC4.genRank J ∧
          SmallerTransitiveRankBound n ∧ ActualResidual J := by
  rcases TraceyOrdinaryRetainedIndexResidual.traceyPermutation_or_actual_minimal_narrow_finite_model
    hCFSG remaining with h | ⟨m,hm,L,ht,hbad,hbelow,_⟩
  · exact Or.inl h
  · letI := ht
    exact Or.inr ⟨m,hm,L,ht,hbad,hbelow,
      actual_residual_of_failed_coarse remaining L hCFSG hm hbad hbelow⟩

end SymmetricSubgroupAsymptotics.TraceyOrdinarySporadicPairResidual
