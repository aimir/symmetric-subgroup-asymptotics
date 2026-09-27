import SymmetricSubgroupAsymptotics.OrbitProfileOrbitCriterion

/-!
# The actual orbit image of a selected full-profile block

The general orbit criterion finds some profile block above a given orbit.
For ownership transport we need the converse direction with the occurrence
label retained: a selected occupied block is itself an actual orbit and its
entire restriction image is the displayed original local action.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.OrbitProfileFullOn

variable {ι X : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {e : OrbitProfilePoints Ω m ≃ X} {H : Subgroup (Equiv.Perm X)}

/-- Exact restriction image for one prescribed occupied block. -/
theorem selected_orbit_image (hH : OrbitProfileFullOn U e H)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (i : ι) (j : Fin (m i)) (x : Ω i) :
    ∃ o : OrbitProfileFromOrbits.Orbit H, ∃ c : Ω i ≃ o.orbit,
      relabelSubgroup c (U i) = OrbitProfileFromOrbits.orbitImage H o := by
  let z : X := e ⟨i,j,x⟩
  let o : OrbitProfileFromOrbits.Orbit H := Quotient.mk'' z
  have hinj : Function.Injective (fun y : Ω i => e ⟨i,j,y⟩) := by
    intro y w h
    have hh := e.injective h
    have hp : (j,y) = (j,w) := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
    exact congrArg Prod.snd hp
  have hb : Set.range (fun y : Ω i => e ⟨i,j,y⟩) = o.orbit := by
    rw [← hH.orbit_eq_block htrans i j x]
    exact (MulAction.orbitRel.Quotient.orbit_mk z).symm
  let c : Ω i ≃ o.orbit :=
    (Equiv.ofInjective (fun y : Ω i => e ⟨i,j,y⟩) hinj).trans (Equiv.setCongr hb)
  have hc (y : Ω i) : (c y : X) = e ⟨i,j,y⟩ := rfl
  have htransport (h : H) (u : U i)
      (hu : ∀ y : Ω i, (h : Equiv.Perm X) (e ⟨i,j,y⟩) =
        e ⟨i,j,(u : Equiv.Perm (Ω i)) y⟩) :
      c.permCongr (u : Equiv.Perm (Ω i)) = MulAction.toPermHom H o.orbit h := by
    apply Equiv.ext
    intro q
    apply Subtype.ext
    change (c ((u : Equiv.Perm (Ω i)) (c.symm q)) : X) =
      (h : Equiv.Perm X) (q : X)
    rw [hc, ← hu]
    have hq : e ⟨i,j,c.symm q⟩ = (q : X) :=
      congrArg Subtype.val (c.apply_symm_apply q)
    exact congrArg (h : Equiv.Perm X) hq
  refine ⟨o,c,?_⟩
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

end SymmetricSubgroupAsymptotics.OrbitProfileFullOn
