import SymmetricSubgroupAsymptotics.MarkedC4OrbitCutoffFamilies
import SymmetricSubgroupAsymptotics.MarkedC4EmbeddedPermutationOrbit

/-! Orbit cutoff survives an actual equivariant point embedding. This
allows deleting fixed points while retaining the bounded nilpotent family,
rather than reverting to an unbounded all-subgroup count. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPermutationOrbitRestriction

/-- Every original orbit injects through the same actual point embedding.
No transitivity or surjectivity of the group map is required. -/
theorem orbit_card_le_of_embedding {X Y : Type} [Finite X] [Finite Y]
    (H : Subgroup (Equiv.Perm X)) (G : Subgroup (Equiv.Perm Y))
    (i : X ↪ Y) (lift : H → G)
    (hact : ∀ (g : H) (x : X),i (g.val x)=(lift g).val (i x)) (x : X) :
    Nat.card (MulAction.orbit H x)≤Nat.card (MulAction.orbit G (i x)) := by
  let code : MulAction.orbit H x → MulAction.orbit G (i x) := fun y =>
    ⟨i y.val,by
      obtain ⟨g,hg⟩ := y.property
      exact ⟨lift g,(hact g x).symm.trans (congrArg i hg)⟩⟩
  apply Nat.card_le_card_of_injective code
  intro y z h
  apply Subtype.ext
  exact i.injective (congrArg (fun u : MulAction.orbit G (i x) => u.val) h)

/-- Point relabelling preserves every actual orbit cutoff, including
fixed points and empty point types. -/
theorem cutoff_map_equiv {X Y : Type} [Finite X] [Finite Y]
    {C : ℕ} (H : Subgroup (Equiv.Perm X)) (e : X ≃ Y)
    (hcut : ∀ x : X,Nat.card (MulAction.orbit H x)<C) :
    ∀ y : Y,Nat.card (MulAction.orbit (H.map e.permCongrHom.toMonoidHom) y)<C := by
  let f := e.permCongrHom.toMonoidHom
  let E := H.equivMapOfInjective f e.permCongrHom.injective
  intro y
  apply (orbit_card_le_of_embedding (H.map f) H e.symm.toEmbedding E.symm
    (by
      intro g x
      obtain ⟨h,rfl⟩ := E.surjective g
      rw [E.symm_apply_apply]
      change e.symm (e ((h.val) (e.symm x)))=h.val (e.symm x)
      exact e.symm_apply_apply _) y).trans_lt
  exact hcut (e.symm y)

end SymmetricSubgroupAsymptotics.CFSGPermutationOrbitRestriction
