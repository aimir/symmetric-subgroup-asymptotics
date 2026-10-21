import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact least proper subgroup index of the alternating family, proved
without classification. A proper-subgroup coset action is faithful by
simplicity. The order n!/2 rules out a smaller permutation degree; an
actual point stabilizer supplies index n. The strict square-order estimate
is an elementary factorial inequality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingMinimumIndex

private theorem twice_card (n : ℕ) (hn : 5≤n) :
    2*Nat.card (alternatingGroup (Fin n))=n.factorial := by
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simp only [Nat.card_fin];omega)
  simpa only [Nat.card_perm,Nat.card_fin] using
    (two_mul_nat_card_alternatingGroup (α := Fin n))

/-- Every proper subgroup of A_n has index at least n, for all n≥5. -/
theorem degree_le_proper_index (n : ℕ) (hn : 5≤n)
    (H : Subgroup (alternatingGroup (Fin n))) (hH : H≠⊤) : n≤H.index := by
  letI : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup
    (by simpa only [Nat.card_fin] using hn)
  have hcore : H.normalCore=⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore H.normalCore_normal with h|h
    · exact h
    · exact (hH (top_le_iff.mp (h ▸ H.normalCore_le))).elim
  let f : alternatingGroup (Fin n) →* Equiv.Perm ((alternatingGroup (Fin n)) ⧸ H) :=
    MulAction.toPermHom (alternatingGroup (Fin n)) ((alternatingGroup (Fin n)) ⧸ H)
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    exact (Subgroup.normalCore_eq_ker H).symm.trans hcore
  have hc : Nat.card (alternatingGroup (Fin n))≤H.index.factorial := by
    simpa only [Nat.card_perm,←H.index_eq_card] using Nat.card_le_card_of_injective f hf
  by_contra hsmall
  have hfac : H.index.factorial≤(n-1).factorial := Nat.factorial_le (by omega)
  have horder := twice_card n hn
  have hnfac : n.factorial=n*(n-1).factorial := by
    simpa only [Nat.sub_add_cancel (by omega : 1≤n)] using Nat.factorial_succ (n-1)
  rw [hnfac] at horder
  have hpos : 0<(n-1).factorial := Nat.factorial_pos _
  nlinarith

/-- The index witness is the original point stabilizer, not an abstract
subgroup whose order happens to match. -/
theorem exists_proper_index_degree (n : ℕ) (hn : 5≤n) :
    ∃ H : Subgroup (alternatingGroup (Fin n)),H≠⊤ ∧ H.index=n := by
  letI : MulAction.IsPretransitive (alternatingGroup (Fin n)) (Fin n) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin n)
      (by simp only [Nat.card_fin];omega)
  let x : Fin n := ⟨0,by omega⟩
  let H := MulAction.stabilizer (alternatingGroup (Fin n)) x
  have hi : H.index=n := by
    simpa only [H,Nat.card_fin] using
      MulAction.index_stabilizer_of_transitive (alternatingGroup (Fin n)) x
  refine ⟨H,?_,hi⟩
  intro he
  rw [he,Subgroup.index_top] at hi
  omega

/-- A_n's literal least proper subgroup index is n. -/
theorem leastProperIndex_degree (n : ℕ) (hn : 5≤n) :
    PrimitiveSocleRawStructure.LeastProperIndex (alternatingGroup (Fin n)) n :=
  ⟨exists_proper_index_degree n hn,degree_le_proper_index n hn⟩

theorem leastProperIndex_eq_degree (n : ℕ) (hn : 5≤n) (ell : ℕ)
    (hell : PrimitiveSocleRawStructure.LeastProperIndex (alternatingGroup (Fin n)) ell) : ell=n := by
  obtain ⟨H,hH,hi⟩ := hell.1
  have hlo : n≤ell := by simpa only [hi] using degree_le_proper_index n hn H hH
  obtain ⟨K,hK,hKi⟩ := exists_proper_index_degree n hn
  have hhi : ell≤n := by simpa only [hKi] using hell.2 K hK
  omega

private theorem twice_square_lt_factorial (n : ℕ) (hn : 5≤n) : 2*n^2<n.factorial := by
  induction n,hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [Nat.factorial_succ]
    have hs : n+1≤n^2 := by nlinarith
    calc
      2*(n+1)^2=(n+1)*(2*(n+1)) := by ring
      _ ≤ (n+1)*(2*n^2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hs)
      _ < (n+1)*n.factorial := Nat.mul_lt_mul_of_pos_left ih (by omega)

/-- The alternating family satisfies the strict least-index square-order
bound directly; no CFSG theorem or numerical catalogue is used. -/
theorem degree_square_lt_card (n : ℕ) (hn : 5≤n) :
    n^2<Nat.card (alternatingGroup (Fin n)) := by
  have hs := twice_square_lt_factorial n hn
  have hc := twice_card n hn
  omega

theorem leastProperIndex_square_lt_card (n : ℕ) (hn : 5≤n) (ell : ℕ)
    (hell : PrimitiveSocleRawStructure.LeastProperIndex (alternatingGroup (Fin n)) ell) :
    ell^2<Nat.card (alternatingGroup (Fin n)) := by
  rw [leastProperIndex_eq_degree n hn ell hell]
  exact degree_square_lt_card n hn

end SymmetricSubgroupAsymptotics.CFSGAlternatingMinimumIndex
