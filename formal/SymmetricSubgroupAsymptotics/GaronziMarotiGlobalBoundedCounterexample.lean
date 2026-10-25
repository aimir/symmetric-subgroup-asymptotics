import SymmetricSubgroupAsymptotics.GaronziMarotiBoundedShapeCFSGReduction
import SymmetricSubgroupAsymptotics.GaronziMarotiTransitiveTarget
import Mathlib.Data.Nat.Find

/-! A global residual without a supplied bounded-degree class callback.
A failed class cube has a least-degree actual permutation counterexample.
The checked induction reduction places it at bounded degree or retains
literal Tits/sporadic data from its original action or block sections. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.GaronziMarotiGlobalBoundedCounterexample
open GaronziMarotiBoundedShapeCFSGReduction

theorem exists_minimal_counterexample
    (n : ℕ) (hn : 4 ≤ n) (L : Subgroup (Equiv.Perm (Fin n)))
    (hbad : 5^(n-1) < Nat.card (ConjClasses L)^3) :
    ∃ m : ℕ, m ≤ n ∧ 4 ≤ m ∧ ∃ H : Subgroup (Equiv.Perm (Fin m)),
      5^(m-1) < Nat.card (ConjClasses H)^3 ∧
      (∀ j : ℕ, j < m → 4 ≤ j → ∀ J : Subgroup (Equiv.Perm (Fin j)),
        Nat.card (ConjClasses J)^3 ≤ 5^(j-1)) := by
  let P : ℕ → Prop := fun j => 4 ≤ j ∧
    ∃ J : Subgroup (Equiv.Perm (Fin j)), 5^(j-1) < Nat.card (ConjClasses J)^3
  have hex : ∃ j, P j := ⟨n,hn,L,hbad⟩
  let m := Nat.find hex
  have hm : P m := Nat.find_spec hex
  obtain ⟨hm4,H,hH⟩ := hm
  refine ⟨m,Nat.find_min' hex ⟨hn,L,hbad⟩,hm4,H,hH,?_⟩
  intro j hj hj4 J
  by_contra hJ
  exact Nat.find_min hex hj ⟨hj4,J,lt_of_not_ge hJ⟩

theorem garonziMaroti_or_bounded_counterexample_or_actual_finite_model
    (hCFSG : CFSG.CFSGClassification) :
    GaronziMarotiConjugacyClassBound ∨
      (∃ n : ℕ, 4 ≤ n ∧ n ≤ 36855 ∧ ∃ L : Subgroup (Equiv.Perm (Fin n)),
        5^(n-1) < Nat.card (ConjClasses L)^3) ∨
      (∃ n : ℕ, 4 ≤ n ∧ ∃ L : Subgroup (Equiv.Perm (Fin n)),
        5^(n-1) < Nat.card (ConjClasses L)^3 ∧ ActualFiniteModelResidual L (Fin n)) := by
  by_cases hcube : ∀ n : ℕ, 4 ≤ n → ∀ L : Subgroup (Equiv.Perm (Fin n)),
      Nat.card (ConjClasses L)^3 ≤ 5^(n-1)
  · left
    intro n hn L
    exact (GaronziMarotiTransitiveTarget.cube_le_iff_real_bound _ n (by omega)).mp
      (hcube n hn L)
  · push_neg at hcube
    obtain ⟨n,hn,L,hbad⟩ := hcube
    obtain ⟨m,_,hm,H,hH,hSmaller⟩ := exists_minimal_counterexample n hn L hbad
    rcases minimal_counterexample_bounded_or_actual_finite_model hCFSG m hm H hH hSmaller with h | h
    · exact Or.inr (Or.inl ⟨m,hm,h,H,hH⟩)
    · exact Or.inr (Or.inr ⟨m,hm,H,hH,h⟩)

end SymmetricSubgroupAsymptotics.GaronziMarotiGlobalBoundedCounterexample
