import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index

/-! Actual permutation-induced automorphisms of A_n. Conjugation by S_n
is injective; its map to the literal outer-automorphism quotient has kernel
A_n and image order two. The remaining outer order is exactly twice the
index of this conjugation image in Aut(A_n). This identity retains the
possible exceptional degree-six overgroup; it does not assert that all
automorphisms are permutation-induced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingOuterAutomorphisms
open PrimitiveSocleRawStructure

abbrev A (n : ℕ) := alternatingGroup (Fin n)

def permutationConjugation (n : ℕ) : Equiv.Perm (Fin n) →* MulAut (A n) :=
  MulAut.conjNormal

/-- A twice-transitive natural alternating action has trivial centralizer
inside the full symmetric group. -/
theorem commuting_permutation_eq_one (n : ℕ) (hn : 5≤n)
    (g : Equiv.Perm (Fin n)) (hcomm : ∀ h : A n,g*h.val=h.val*g) : g=1 := by
  letI : MulAction.IsMultiplyPretransitive (A n) (Fin n) (n-2) := by
    simpa only [Nat.card_fin] using alternatingGroup.isMultiplyPretransitive (Fin n)
  letI : MulAction.IsMultiplyPretransitive (A n) (Fin n) 2 :=
    MulAction.isMultiplyPretransitive_of_le (by omega : 2≤n-2) (by simp only [Nat.card_fin];omega)
  apply Equiv.ext
  intro a
  change g a=a
  by_contra hga
  have hbcard : 0<(({a,g a} : Finset (Fin n))ᶜ).card := by
    rw [Finset.card_compl,Fintype.card_fin,Finset.card_pair (Ne.symm hga)]
    omega
  obtain ⟨b,hb⟩ := Finset.card_pos.mp hbcard
  have hba : b≠a ∧ b≠g a := by
    simpa only [Finset.mem_compl,Finset.mem_insert,Finset.mem_singleton,not_or] using hb
  obtain ⟨h,hha,hhga⟩ := (MulAction.is_two_pretransitive_iff.mp
    (inferInstance : MulAction.IsMultiplyPretransitive (A n) (Fin n) 2)) (Ne.symm hga) hba.1.symm
  change h.val a=a at hha
  change h.val (g a)=b at hhga
  have he := congrArg (fun p : Equiv.Perm (Fin n) => p a) (hcomm h)
  change g (h.val a)=h.val (g a) at he
  rw [hha,hhga] at he
  exact hba.2 he.symm

theorem permutationConjugation_injective (n : ℕ) (hn : 5≤n) :
    Function.Injective (permutationConjugation n) := by
  apply (permutationConjugation n).ker_eq_bot_iff.mp
  apply bot_unique
  intro g hg
  change g=1
  apply commuting_permutation_eq_one n hn g
  intro h
  have he := congrArg (fun a : MulAut (A n) => a h) hg
  have hp := congrArg (fun a : A n => a.val) he
  change g*h.val*g⁻¹=h.val at hp
  have hm := congrArg (fun p : Equiv.Perm (Fin n) => p*g) hp
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hm

/-- The actual inner automorphisms lie in the actual permutation-induced
image, with the original element as their point-permutation witness. -/
theorem inner_le_permutationConjugation_range (n : ℕ) :
    Inner (A n)≤(permutationConjugation n).range := by
  rintro a ⟨g,rfl⟩
  exact ⟨g.val,MulAut.conjNormal_val⟩

def permutationOuter (n : ℕ) : Equiv.Perm (Fin n) →* Outer (A n) :=
  (QuotientGroup.mk' (Inner (A n))).comp (permutationConjugation n)

theorem permutationOuter_ker (n : ℕ) (hn : 5≤n) :
    (permutationOuter n).ker=alternatingGroup (Fin n) := by
  ext g
  change (QuotientGroup.mk' (Inner (A n))) (permutationConjugation n g)=1 ↔ g∈alternatingGroup (Fin n)
  change permutationConjugation n g ∈ (QuotientGroup.mk' (Inner (A n))).ker ↔ _
  rw [QuotientGroup.ker_mk']
  constructor
  · rintro ⟨a,ha⟩
    have he : permutationConjugation n g=permutationConjugation n a.val :=
      ha.symm.trans (MulAut.conjNormal_val).symm
    have hg := permutationConjugation_injective n hn he
    rw [hg]
    exact a.property
  · intro hg
    exact ⟨⟨g,hg⟩,(MulAut.conjNormal_val).symm⟩

theorem permutationOuter_range_card (n : ℕ) (hn : 5≤n) :
    Nat.card (permutationOuter n).range=2 := by
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simp only [Nat.card_fin];omega)
  rw [←Subgroup.index_ker,permutationOuter_ker n hn]
  exact alternatingGroup.index_eq_two

/-- This exact factor exposes the remaining automorphism-recognition
obligation and leaves room for the exceptional degree-six factor. -/
theorem outer_card_eq_two_mul_permutationConjugation_index (n : ℕ) (hn : 5≤n) :
    Nat.card (Outer (A n))=2*(permutationConjugation n).range.index := by
  let q := QuotientGroup.mk' (Inner (A n))
  have hi : (permutationOuter n).range.index=(permutationConjugation n).range.index := by
    change ((q.comp (permutationConjugation n)).range).index=_
    rw [MonoidHom.range_comp]
    apply Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _)
    rw [QuotientGroup.ker_mk']
    exact inner_le_permutationConjugation_range n
  have hc := (permutationOuter n).range.card_mul_index
  rw [permutationOuter_range_card n hn,hi] at hc
  exact hc.symm

end SymmetricSubgroupAsymptotics.CFSGAlternatingOuterAutomorphisms
