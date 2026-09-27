import SymmetricSubgroupAsymptotics.OrbitProfileFromOrbits

/-!
# Full profiles and the images on the literal original orbits

A full original profile supplies an exact point chart for every actual
orbit image. Together with the simultaneous orbit constructor, this gives
an iff with no product-independence, action-separation, or counting input.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace OrbitProfileFullOn

variable {ι X : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {e : OrbitProfilePoints Ω m ≃ X} {H : Subgroup (Equiv.Perm X)}

/-- Every actual orbit receives the chart of its original occupied block.
The equality identifies the entire restriction image, not an abstract
group isomorphism or just its cardinality. -/
theorem orbit_image_chart (hH : OrbitProfileFullOn U e H)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (o : OrbitProfileFromOrbits.Orbit H) :
    ∃ i, ∃ j : Fin (m i), ∃ c : Ω i ≃ o.orbit,
      relabelSubgroup c (U i) = OrbitProfileFromOrbits.orbitImage H o := by
  obtain ⟨⟨i,j,x⟩,hx⟩ := e.surjective o.out
  have hinj : Function.Injective (fun y : Ω i => e ⟨i,j,y⟩) := by
    intro y z h
    have hh := e.injective h
    have hp : (j,y) = (j,z) := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
    exact congrArg Prod.snd hp
  have hb : Set.range (fun y : Ω i => e ⟨i,j,y⟩) = o.orbit := by
    rw [← hH.orbit_eq_block htrans i j x,hx,
      o.orbit_eq_orbit_out Quotient.out_eq']
  let c : Ω i ≃ o.orbit :=
    (Equiv.ofInjective (fun y : Ω i => e ⟨i,j,y⟩) hinj).trans (Equiv.setCongr hb)
  have hc (y : Ω i) : (c y : X) = e ⟨i,j,y⟩ := rfl
  have htransport (h : H) (u : U i)
      (hu : ∀ y : Ω i, (h : Equiv.Perm X) (e ⟨i,j,y⟩) =
        e ⟨i,j,(u : Equiv.Perm (Ω i)) y⟩) :
      c.permCongr (u : Equiv.Perm (Ω i)) = MulAction.toPermHom H o.orbit h := by
    apply Equiv.ext
    intro z
    apply Subtype.ext
    change (c ((u : Equiv.Perm (Ω i)) (c.symm z)) : X) =
      (h : Equiv.Perm X) (z : X)
    rw [hc, ← hu]
    have hz : e ⟨i,j,c.symm z⟩ = (z : X) :=
      congrArg Subtype.val (c.apply_symm_apply z)
    exact congrArg (h : Equiv.Perm X) hz
  refine ⟨i,j,c,?_⟩
  ext v
  change v ∈ (U i).map c.permCongrHom.toMonoidHom ↔
    v ∈ (MulAction.toPermHom H o.orbit).range
  constructor
  · rintro ⟨u,hu,rfl⟩
    obtain ⟨h,hh⟩ := hH.full i j ⟨u,hu⟩
    exact ⟨h,(htransport h ⟨u,hu⟩ hh).symm⟩
  · rintro ⟨h,rfl⟩
    obtain ⟨u,hu⟩ := hH.maps h i j
    exact ⟨u.val,u.property,htransport h u hu⟩

end OrbitProfileFullOn

namespace OrbitProfileFromOrbits

variable {ι X : Type*} {Ω : ι → Type*} [Finite X]
    (H : Subgroup (Equiv.Perm X)) (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))

/-- An intrinsic criterion for existence of some full original profile.
Only local transitivity is required; the original H is never replaced by
the independent product of its orbit images. -/
theorem exists_profile_iff_orbit_images
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y) :
    (∃ m : ι → ℕ, ∃ e : OrbitProfilePoints Ω m ≃ X, OrbitProfileFullOn U e H) ↔
      ∀ o : Orbit H, ∃ i, ∃ e : Ω i ≃ o.orbit,
        relabelSubgroup e (U i) = orbitImage H o := by
  constructor
  · rintro ⟨m,e,he⟩ o
    obtain ⟨i,j,c,hc⟩ := he.orbit_image_chart htrans o
    exact ⟨i,c,hc⟩
  · exact exists_profile_of_orbit_charts H U

end OrbitProfileFromOrbits

end SymmetricSubgroupAsymptotics

end
