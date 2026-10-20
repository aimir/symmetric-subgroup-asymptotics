import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput
import Mathlib.RepresentationTheory.Maschke
import Mathlib.Order.Preorder.Finite

/-! Irreducible extraction for the finite complex faithful-character proof.
A tuple of nonzero envelopes which excludes fixed vectors for every actual
minimal normal subgroup yields a jointly faithful tuple of irreducibles.
No character-selection or socle-generation theorem is assumed here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.ZmudFixedSpaceConstituents

/-- A finite complex representation before choosing an irreducible constituent. -/
structure Envelope (G : Type) [Group G] where
  Space : Type
  [addCommGroup : AddCommGroup Space]
  [module : Module ℂ Space]
  [finiteDimensional : FiniteDimensional ℂ Space]
  [nontrivial : Nontrivial Space]
  action : Representation ℂ G Space

attribute [instance] Envelope.addCommGroup Envelope.module
  Envelope.finiteDimensional Envelope.nontrivial

variable {G : Type} [Group G] [Finite G]

/-- The finite complex envelope has an actual irreducible constituent
injected by its original representation map. -/
theorem exists_irreducible_injection (E : Envelope G) :
    ∃ r : FiniteIrreducibleRepresentation ℂ G,
      ∃ j : r.action.IntertwiningMap E.action, Function.Injective j := by
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast (Nat.card_pos (α := G)).ne'⟩
  let rho := E.action
  letI : Nontrivial rho.asModule := rho.asModuleEquiv.toEquiv.nontrivial
  obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule ℂ[G] rho.asModule
  let tau := (Subrepresentation.ofSubmodule' S).toRepresentation
  letI : IsSimpleModule ℂ[G] S := hS
  have ht : IsSimpleModule ℂ[G] tau.asModule :=
    (submoduleRepresentationModuleEquiv rho S).toLinearMap.isSimpleModule_iff_of_bijective
      (submoduleRepresentationModuleEquiv rho S).bijective |>.mp hS
  let r : FiniteIrreducibleRepresentation ℂ G :=
    { Space := (Subrepresentation.ofSubmodule' S).toSubmodule
      addCommGroup := inferInstance
      module := inferInstance
      finiteDimensional := inferInstance
      action := tau
      irreducible := (Representation.irreducible_iff_isSimpleModule_asModule tau).mpr ht }
  let j : r.action.IntertwiningMap E.action :=
    { toLinearMap := (Subrepresentation.ofSubmodule' S).toSubmodule.subtype
      isIntertwining' _ := rfl }
  exact ⟨r, j, Subtype.val_injective⟩

private theorem minimalNormal_le
    (K : Subgroup G) [K.Normal] (hK : K ≠ ⊥) :
    ∃ N : Subgroup G, IsMinimalNormalSubgroup N ∧ N ≤ K := by
  let good : Subgroup G → Prop := fun N => N.Normal ∧ N ≠ ⊥
  obtain ⟨N, hNK, hN⟩ := Finite.exists_le_minimal
    (p := good) (a := K) ⟨inferInstance, hK⟩
  refine ⟨N, ⟨hN.1.1, hN.1.2, ?_⟩, hNK⟩
  intro M hMn hMne hMN
  exact hN.eq_of_le ⟨hMn, hMne⟩ hMN

/-- Any irreducible choices inside the given envelopes remain jointly
faithful when every nontrivial minimal normal subgroup has a fixed-free
slot.  The empty tuple is included. -/
theorem exists_jointly_faithful_irreducibles
    (t : ℕ) (E : Fin t → Envelope G)
    (hfixed : ∀ N : Subgroup G, IsMinimalNormalSubgroup N →
      ∃ i : Fin t, ∀ v : (E i).Space,
        (∀ n : N, (E i).action n.val v = v) → v = 0) :
    ∃ r : Fin t → FiniteIrreducibleRepresentation ℂ G,
      ∀ g : G, (∀ i, (r i).action g = 1) → g = 1 := by
  choose r j hj using fun i => exists_irreducible_injection (E i)
  let K : Subgroup G := ⨅ i : Fin t, (r i).action.asGroupHom.ker
  letI : K.Normal := Subgroup.normal_iInf_normal (fun _ => inferInstance)
  have hK : K = ⊥ := by
    by_contra hK
    obtain ⟨N, hN, hNK⟩ := minimalNormal_le K hK
    obtain ⟨i, hi⟩ := hfixed N hN
    letI : Nontrivial (r i).action.asModule :=
      IsSimpleModule.nontrivial ℂ[G] (r i).action.asModule
    letI : Nontrivial (r i).Space :=
      (r i).action.asModuleEquiv.toEquiv.symm.nontrivial
    obtain ⟨w, hw⟩ := exists_ne (0 : (r i).Space)
    have hz : j i w = 0 := hi (j i w) (by
      intro n
      have hk : n.val ∈ (r i).action.asGroupHom.ker :=
        Subgroup.mem_iInf.mp (hNK n.property) i
      have haction : (r i).action n.val = 1 :=
        congrArg Units.val (MonoidHom.mem_ker.mp hk)
      have he := Representation.IntertwiningMap.isIntertwining
        (r i).action (E i).action (j i) n.val w
      rw [haction, Module.End.one_apply] at he
      exact he.symm)
    exact hw (hj i (hz.trans (j i).map_zero.symm))
  refine ⟨r, ?_⟩
  intro g hg
  have hgK : g ∈ K := by
    apply Subgroup.mem_iInf.mpr
    intro i
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    exact hg i
  rw [hK, Subgroup.mem_bot] at hgK
  exact hgK

end SymmetricSubgroupAsymptotics.ZmudFixedSpaceConstituents
