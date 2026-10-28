import SymmetricSubgroupAsymptotics.CFSGCatalogueWithAxiomMonster
import SymmetricSubgroupAsymptotics.CFSGAxiomMonsterY443SmallAction
import SymmetricSubgroupAsymptotics.PrimitiveSocleNonpairDegreeTwentyFour
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexPacketOrTitsSporadic

/-! Exact small-degree classification funnels used by bounded-sharp proofs.
The new raw factor is excluded by its actual degree>=27; all returned model
witnesses belong to the historical non-M branch. No new small-action census,
ordinary-rank input, numerical callback or old classification is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueSmallDegreeModels
open PrimitiveSocleRawStructure CFSGReduction
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction (RemainingModel)

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

/-- Same conclusion as the checked old small-degree model/pair funnel. -/
theorem pair_family_or_actual_remaining_of_degree_below_twenty_four
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hr : Nat.card X<24) :
    (∃ j : CFSG.Index,PairFamily j ∧ Nonempty (D.Simple≃*j.Model)) ∨
      ∃ j : CFSG.Index,RemainingModel j ∧ Nonempty (D.Simple≃*j.Model) := by
  obtain ⟨i,e⟩ := CFSGCatalogueWithAxiomMonster.modelWitness hclass D.Simple
  cases i with
  | inl i =>
    let e0 : D.Simple ≃* i.val.Model := e
    by_cases hp : PairFamily i.val
    · exact Or.inl ⟨i.val,hp,⟨e0⟩⟩
    by_cases hf : RemainingModel i.val
    · exact Or.inr ⟨i.val,hf,⟨e0⟩⟩
    have hd := PrimitiveSocleNonpairDegreeTwentyFour.degree_ge_twenty_four_of_nonpair D i.val e0 hp hf
    omega
  | inr u =>
    have hd := CFSGAxiomMonsterY443SmallAction.degree_ge_twentySeven D e
    omega

/-- The degree-five frontend needs the actual index packet rather than a pair. -/
theorem factor_packet_or_actual_remaining_of_degree_below_twentySeven
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hr : Nat.card X<27) :
    (∀ ell : ℕ,LeastProperIndex D.Simple ell → ell^2<Nat.card D.Simple ∧
      SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) ∨
      ∃ j : CFSG.Index,RemainingModel j ∧ Nonempty (D.Simple≃*j.Model) := by
  obtain ⟨i,e⟩ := CFSGCatalogueWithAxiomMonster.modelWitness hclass D.Simple
  cases i with
  | inl i =>
    let e0 : D.Simple ≃* i.val.Model := e
    letI : Finite i.val.Model := Finite.of_equiv D.Simple e0.toEquiv
    letI : IsSimpleGroup i.val.Model := e0.symm.isSimpleGroup
    have hn : ¬IsMulCommutative i.val.Model :=
      fun hc => D.noncommutative ((isMulCommutative_congr e0).mpr hc)
    rcases CFSGSimpleIndexPacketOrTitsSporadic.model_packet_or_remaining i.val hn with hp | hi
    · exact Or.inl (sufficientSimpleIndexBounds_of_mulEquiv e0 hp)
    · exact Or.inr ⟨i.val,hi,⟨e0⟩⟩
  | inr u =>
    have hd := CFSGAxiomMonsterY443SmallAction.degree_ge_twentySeven D e
    omega

end SymmetricSubgroupAsymptotics.ExtendedCatalogueSmallDegreeModels
