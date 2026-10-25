import SymmetricSubgroupAsymptotics.TransitiveOrdinaryLieCFSGReduction
import Mathlib.Data.Nat.Find

/-! A global ordinary-generator residual without an induction callback.
Any failed coarse transitive bound has a least-degree ACTUAL transitive
permutation counterexample. Smaller transitive degrees then satisfy the
bound by minimality, and the checked reduction retains literal original
primitive/block Tits-sporadic data. This disjunction does not assert the
remaining finite-model bounds or the complete Tracey theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TraceyOrdinaryGlobalFiniteModelCounterexample
open TraceyStrictlySmallerTransitiveActions TransitiveOrdinaryLieCFSGReduction

theorem exists_minimal_counterexample
    (n : ℕ) (hn : 2 ≤ n) (J : Subgroup (Equiv.Perm (Fin n)))
    (ht : MulAction.IsPretransitive J (Fin n))
    (hbad : traceyPermutationGeneratorCeiling n < MarkedC4.genRank J) :
    ∃ m : ℕ, m ≤ n ∧ 2 ≤ m ∧ ∃ H : Subgroup (Equiv.Perm (Fin m)),
      MulAction.IsPretransitive H (Fin m) ∧
      traceyPermutationGeneratorCeiling m < MarkedC4.genRank H ∧
      SmallerTransitiveRankBound m := by
  let P : ℕ → Prop := fun j => 2 ≤ j ∧
    ∃ H : Subgroup (Equiv.Perm (Fin j)), MulAction.IsPretransitive H (Fin j) ∧
      traceyPermutationGeneratorCeiling j < MarkedC4.genRank H
  have hex : ∃ j, P j := ⟨n,hn,J,ht,hbad⟩
  let m := Nat.find hex
  obtain ⟨hm,H,hHtrans,hHbad⟩ := Nat.find_spec hex
  refine ⟨m,Nat.find_min' hex ⟨hn,J,ht,hbad⟩,hm,H,hHtrans,hHbad,?_⟩
  intro k hk K hk2 hKtrans
  by_contra hK
  exact Nat.find_min hex hk ⟨hk2,K,hKtrans,lt_of_not_ge hK⟩

theorem minimal_counterexample_has_actual_finite_model
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hn : 2 ≤ n)
    (J : Subgroup (Equiv.Perm (Fin n))) [MulAction.IsPretransitive J (Fin n)]
    (hbad : traceyPermutationGeneratorCeiling n < MarkedC4.genRank J)
    (hbelow : SmallerTransitiveRankBound n) : ActualFiniteModelResidual J := by
  rcases genRank_le_ceiling_or_actual_finite_model J hCFSG hn hbelow with h | h
  · exact (not_lt_of_ge h hbad).elim
  · exact h

theorem traceyPermutation_or_actual_minimal_finite_model
    (hCFSG : CFSG.CFSGClassification) :
    TraceyPermutationGeneratorInput ∨
      ∃ n : ℕ, 2 ≤ n ∧ ∃ J : Subgroup (Equiv.Perm (Fin n)),
        ∃ ht : MulAction.IsPretransitive J (Fin n),
          letI := ht
          traceyPermutationGeneratorCeiling n < MarkedC4.genRank J ∧
          SmallerTransitiveRankBound n ∧ ActualFiniteModelResidual J := by
  by_cases hall : ∀ n : ℕ, 2 ≤ n → ∀ J : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPretransitive J (Fin n) →
        MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n
  · left
    intro n J hn ht
    obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact ⟨S,hgen,hS.le.trans (hall n hn J ht)⟩
  · push_neg at hall
    obtain ⟨n,hn,J,ht,hbad⟩ := hall
    obtain ⟨m,_,hm,H,hHtrans,hHbad,hSmaller⟩ := exists_minimal_counterexample n hn J ht hbad
    letI := hHtrans
    exact Or.inr ⟨m,hm,H,hHtrans,hHbad,hSmaller,
      minimal_counterexample_has_actual_finite_model hCFSG m hm H hHbad hSmaller⟩

end SymmetricSubgroupAsymptotics.TraceyOrdinaryGlobalFiniteModelCounterexample
