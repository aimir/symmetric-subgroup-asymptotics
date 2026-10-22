import SymmetricSubgroupAsymptotics.CFSGA2SingerDerivedRoot
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Center

/-! Actual selected four-root words and opposition give derived elements
in their generated subgroup, then in any actual source action image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGA2SingerGeneratedDerived
variable {G : Type*} [Group G]

def selectedGroup (root : Bool→Fin 2→G) : Subgroup G :=
  Subgroup.closure (Set.range (fun p : Bool×Fin 2=>root p.1 p.2))

private def selectedRoot (root : Bool→Fin 2→G) (neg : Bool) (i : Fin 2) : selectedGroup root :=
  ⟨root neg i,Subgroup.subset_closure ⟨(neg,i),rfl⟩⟩

theorem roots_mem_selected_commutator (root : Bool→Fin 2→G) (omega : G)
    (hsquare : ∀neg i,(root neg i)^2=1)
    (hthree : ((root false 0*root true 0*root false 0)*
      (root false 1*root true 1*root false 1))^3=1)
    (hseven : (root false 0*(root false 0*root true 0*root false 0)*
      (root false 1*root true 1*root false 1))^7=1)
    (hopposition : ∀neg i,omega*root neg i*omega⁻¹=root (!neg) i)
    (neg : Bool) : root neg 0∈⁅selectedGroup root,selectedGroup root⁆ := by
  have hi : selectedRoot root false 0∈commutator (selectedGroup root) := by
    apply CFSGA2SingerDerivedRoot.root_mem_commutator
      (selectedRoot root false 0) (selectedRoot root true 0)
      (selectedRoot root false 1) (selectedRoot root true 1)
    · exact Subtype.ext (hsquare false 0)
    · exact Subtype.ext (hsquare true 0)
    · exact Subtype.ext (hsquare false 1)
    · exact Subtype.ext (hsquare true 1)
    · exact Subtype.ext hthree
    · exact Subtype.ext hseven
  have hpos : root false 0∈⁅selectedGroup root,selectedGroup root⁆ := by
    rw [←Subgroup.map_subtype_commutator]
    exact ⟨selectedRoot root false 0,hi,rfl⟩
  cases neg
  · exact hpos
  · let c : G→*G := (MulAut.conj omega).toMonoidHom
    have hc : ∀neg i,c (root neg i)=root (!neg) i := hopposition
    have hL : (selectedGroup root).map c≤selectedGroup root := by
      rw [selectedGroup,MonoidHom.map_closure]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨x,⟨p,rfl⟩,rfl⟩
      rw [hc]
      exact Subgroup.subset_closure ⟨(!p.1,p.2),rfl⟩
    have hh : c (root false 0)∈(⁅selectedGroup root,selectedGroup root⁆).map c :=
      ⟨root false 0,hpos,rfl⟩
    rw [Subgroup.map_commutator] at hh
    have hout := (Subgroup.commutator_mono hL hL) hh
    simpa only [hc] using hout

theorem exists_original_derived_preimage {S : Type*} [Group S] (f : S→*G)
    (root : Bool→Fin 2→G) (omega : G)
    (hsource : ∀neg i,root neg i∈f.range)
    (hsquare : ∀neg i,(root neg i)^2=1)
    (hthree : ((root false 0*root true 0*root false 0)*
      (root false 1*root true 1*root false 1))^3=1)
    (hseven : (root false 0*(root false 0*root true 0*root false 0)*
      (root false 1*root true 1*root false 1))^7=1)
    (hopposition : ∀neg i,omega*root neg i*omega⁻¹=root (!neg) i)
    (neg : Bool) : ∃x : commutator S,f x.val=root neg 0 := by
  have hL : selectedGroup root≤f.range := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨p,rfl⟩
    exact hsource p.1 p.2
  have hh := roots_mem_selected_commutator root omega hsquare hthree hseven hopposition neg
  have hm := (Subgroup.commutator_mono hL hL) hh
  rw [←map_commutator_eq S f] at hm
  rcases hm with ⟨x,hx,he⟩
  exact ⟨⟨x,hx⟩,he⟩

end SymmetricSubgroupAsymptotics.CFSGA2SingerGeneratedDerived
