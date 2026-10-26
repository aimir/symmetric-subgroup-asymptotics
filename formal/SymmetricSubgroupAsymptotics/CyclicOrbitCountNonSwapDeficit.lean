import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead
import Mathlib.GroupTheory.Perm.Sign

/-! A nonidentity, nontransposition moves enough points to delete TWO
points while retaining a representative of every original cyclic orbit.
The acting group and its action remain literal; no cycle census is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CyclicOrbitCountNonSwapDeficit

variable {G X : Type*} [Group G] [MulAction G X] [Finite X]

/-- A nonidentity permutation that is not a swap has a moved point outside
one selected point and its image. -/
theorem exists_two_deletable (g : G)
    (hne : MulAction.toPermHom G X g≠1)
    (hns : ¬(MulAction.toPermHom G X g).IsSwap) :
    ∃ a b : X, g•a≠a ∧ g•b≠b ∧ b≠a ∧ b≠g•a := by
  letI : Fintype X := Fintype.ofFinite X
  let s := MulAction.toPermHom G X g
  have ha : ∃ a : X, s a≠a := by
    by_contra h
    push Not at h
    apply hne
    exact Equiv.ext h
  obtain ⟨a,ha⟩ := ha
  have hb : ∃ b∈s.support, b≠a ∧ b≠s a := by
    by_contra h
    have hsub : s.support⊆{a,s a} := by
      intro b hb
      by_contra hnot
      have hn : b≠a ∧ b≠s a := by simpa only [Finset.mem_insert,
        Finset.mem_singleton,not_or] using hnot
      exact h ⟨b,hb,hn⟩
    have hupper : s.support.card≤2 :=
      (Finset.card_le_card hsub).trans
        ((Finset.card_insert_le a {s a}).trans_eq (by simp))
    have hlower : 2≤s.support.card :=
      Equiv.Perm.two_le_card_support_of_ne_one (show s≠1 from hne)
    have hc : s.support.card=2 := by omega
    have hs : s.IsSwap := Equiv.Perm.card_support_eq_two.mp hc
    exact hns hs
  obtain ⟨b,hb,hba,hbsa⟩ := hb
  exact ⟨a,b,ha,Equiv.Perm.mem_support.mp hb,hba,hbsa⟩

/-- The actual cyclic-orbit quotient loses at least two points whenever
its inducing permutation is neither the identity nor a transposition. -/
theorem cyclic_orbit_card_le_sub_two (g : G)
    (hne : MulAction.toPermHom G X g≠1)
    (hns : ¬(MulAction.toPermHom G X g).IsSwap) :
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) X)≤Nat.card X-2 := by
  letI : Fintype X := Fintype.ofFinite X
  obtain ⟨a,b,ha,hb,hba,hbga⟩ := exists_two_deletable g hne hns
  let O := MulAction.orbitRel.Quotient (Subgroup.zpowers g) X
  let q : X→O := Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) X)
  have hstep : ∀x,q (g•x)=q x := by
    intro x
    apply Quotient.sound
    exact ⟨⟨g,Subgroup.mem_zpowers g⟩,rfl⟩
  let S : Finset X := (Finset.univ.erase a).erase b
  have hmem : ∀x,x∈S ↔ x≠a ∧ x≠b := by
    intro x
    simp only [S,Finset.mem_erase,Finset.mem_univ,and_true]
    exact and_comm
  let f : S→O := fun x => q x.val
  have hf : Function.Surjective f := by
    intro o
    induction o using Quotient.inductionOn with
    | h x =>
      change ∃y:S,q y.val=q x
      by_cases hxa : x=a
      · subst x
        refine ⟨⟨g•a,(hmem _).mpr ⟨ha,Ne.symm hbga⟩⟩,hstep a⟩
      · by_cases hxb : x=b
        · subst x
          by_cases hg : g•b=a
          · refine ⟨⟨g•a,(hmem _).mpr ⟨ha,Ne.symm hbga⟩⟩,?_⟩
            exact (hstep a).trans ((congrArg q hg).symm.trans (hstep b))
          · exact ⟨⟨g•b,(hmem _).mpr ⟨hg,hb⟩⟩,hstep b⟩
        · exact ⟨⟨x,(hmem _).mpr ⟨hxa,hxb⟩⟩,rfl⟩
  have hcard : Nat.card S=Nat.card X-2 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    change ((Finset.univ.erase a).erase b).card=Nat.card X-2
    rw [Finset.card_erase_of_mem (by simp [hba]),
      Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ,
      ←Nat.card_eq_fintype_card]
    omega
  exact (Nat.card_le_card_of_surjective f hf).trans_eq hcard

end SymmetricSubgroupAsymptotics.CyclicOrbitCountNonSwapDeficit
