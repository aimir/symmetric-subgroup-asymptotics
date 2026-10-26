import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

/-! A moved point can be deleted without losing any cyclic orbit. This
uses the literal action and requires neither a cycle classification nor
transitivity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CyclicOrbitCountMovedPointDeficit

variable {G X : Type*} [Group G] [MulAction G X] [Finite X]

theorem cyclic_orbit_card_le_sub_one (g : G)
    (hne : MulAction.toPermHom G X g ≠ 1) :
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) X) ≤ Nat.card X-1 := by
  letI : Fintype X := Fintype.ofFinite X
  obtain ⟨a,ha⟩ : ∃ a : X, g • a ≠ a := by
    by_contra h
    push Not at h
    exact hne (Equiv.ext h)
  let O := MulAction.orbitRel.Quotient (Subgroup.zpowers g) X
  let q : X → O := Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) X)
  have hstep : q (g • a)=q a := by
    apply Quotient.sound
    exact ⟨⟨g,Subgroup.mem_zpowers g⟩,rfl⟩
  let S : Finset X := Finset.univ.erase a
  let f : S → O := fun x => q x.val
  have hf : Function.Surjective f := by
    intro o
    induction o using Quotient.inductionOn with
    | h x =>
      change ∃ y : S, q y.val=q x
      by_cases hx : x=a
      · subst x
        exact ⟨⟨g • a,by simp [S,ha]⟩,hstep⟩
      · exact ⟨⟨x,by simp [S,hx]⟩,rfl⟩
  have hcard : Nat.card S=Nat.card X-1 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    change (Finset.univ.erase a).card=Nat.card X-1
    rw [Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ,
      ←Nat.card_eq_fintype_card]
  exact (Nat.card_le_card_of_surjective f hf).trans_eq hcard

end SymmetricSubgroupAsymptotics.CyclicOrbitCountMovedPointDeficit
