import SymmetricSubgroupAsymptotics.FusionOrbitProfileChart

/-!
# Literal orbits after deleting one invariant orbit

The second restriction image in an actual orbit/complement chart acts on
exactly the unselected original orbits.  This file constructs the orbit
equivalence and identifies the complete induced permutation image.  It is a
structural statement about the unchanged complement; no independence of the
two restriction coordinates is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.FusionOrbitProfileChart
namespace Complement

variable {X Ω Z : Type*} [Fintype X] [Fintype Ω] [Fintype Z]
    (H : Subgroup (Equiv.Perm X))
    (selected : OrbitProfileFromOrbits.Orbit H)
    (eO : Ω ≃ selected.orbit)
    (eC : Z ≃ ↥((orbitSubaction H selected)ᶜ))

/-- The literal image of the original group on the whole complement of the
selected orbit. -/
abbrev image : Subgroup (Equiv.Perm Z) :=
  (secondHom H selected eC).range

/-- A complement-image orbit, viewed as the corresponding original orbit. -/
def ambientOrbit (o : OrbitProfileFromOrbits.Orbit (image H selected eC)) :
    OrbitProfileFromOrbits.Orbit H :=
  Quotient.mk'' ((eC o.out : ↥((orbitSubaction H selected)ᶜ)) : X)

/-- The complement chart identifies the literal point sets of a complement
orbit and its original ambient orbit. -/
def orbitEquiv
    (o : OrbitProfileFromOrbits.Orbit (image H selected eC)) :
    o.orbit ≃ (ambientOrbit H selected eC o).orbit := by
  let f : o.orbit → (ambientOrbit H selected eC o).orbit := fun a =>
    ⟨((eC a.1 : ↥((orbitSubaction H selected)ᶜ)) : X), by
      rw [ambientOrbit, MulAction.orbitRel.Quotient.orbit_mk]
      have ha : a.1 ∈ MulAction.orbit (image H selected eC) o.out := by
        rw [← o.orbit_eq_orbit_out Quotient.out_eq']
        exact a.property
      obtain ⟨g, hg⟩ := ha
      obtain ⟨h, hh⟩ := g.property
      refine ⟨h, ?_⟩
      change (h : Equiv.Perm X)
          ((eC o.out : ↥((orbitSubaction H selected)ᶜ)) : X) =
        ((eC a.1 : ↥((orbitSubaction H selected)ᶜ)) : X)
      have hga : (g : Equiv.Perm Z) o.out = a.1 := hg
      rw [← hh] at hga
      change eC.symm
          ⟨(h : Equiv.Perm X)
              ((eC o.out : ↥((orbitSubaction H selected)ᶜ)) : X), _⟩ =
        a.1 at hga
      have he := congrArg
        (fun z : Z => ((eC z : ↥((orbitSubaction H selected)ᶜ)) : X)) hga
      simpa only [Equiv.apply_symm_apply] using he⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    have habX := congrArg Subtype.val hab
    change ((eC a.1 : ↥((orbitSubaction H selected)ᶜ)) : X) =
      ((eC b.1 : ↥((orbitSubaction H selected)ᶜ)) : X) at habX
    apply Subtype.ext
    apply eC.injective
    exact Subtype.ext habX
  · intro z
    have hz : z.1 ∈ MulAction.orbit H
        ((eC o.out : ↥((orbitSubaction H selected)ᶜ)) : X) := by
      rw [← MulAction.orbitRel.Quotient.orbit_mk]
      exact z.property
    obtain ⟨h, hh⟩ := hz
    have hmem : (h : Equiv.Perm X)
        ((eC o.out : ↥((orbitSubaction H selected)ᶜ)) : X) ∈
          ((orbitSubaction H selected)ᶜ : Set X) := by
      have hs : ((eC o.out : ↥((orbitSubaction H selected)ᶜ)) : X) ∉
          selected.orbit := (eC o.out).property
      intro hselected
      have hback := selected.mapsTo_smul_orbit h⁻¹ hselected
      have heq : (h⁻¹ : H) •
          ((h : Equiv.Perm X)
            ((eC o.out : ↥((orbitSubaction H selected)ᶜ)) : X)) =
          ((eC o.out : ↥((orbitSubaction H selected)ᶜ)) : X) := by
        change (h : Equiv.Perm X)⁻¹
            ((h : Equiv.Perm X)
              ((eC o.out : ↥((orbitSubaction H selected)ᶜ)) : X)) = _
        exact (h : Equiv.Perm X).symm_apply_apply _
      exact hs (heq ▸ hback)
    let a : o.orbit :=
      ⟨eC.symm ⟨(h : Equiv.Perm X)
          ((eC o.out : ↥((orbitSubaction H selected)ᶜ)) : X), hmem⟩, by
        rw [o.orbit_eq_orbit_out Quotient.out_eq']
        let g : image H selected eC :=
          ⟨secondHom H selected eC h, ⟨h, rfl⟩⟩
        refine ⟨g, ?_⟩
        change eC.symm
            ⟨(h : Equiv.Perm X)
                ((eC o.out : ↥((orbitSubaction H selected)ᶜ)) : X), _⟩ = _
        rfl⟩
    refine ⟨a, Subtype.ext ?_⟩
    change ((eC a.1 : ↥((orbitSubaction H selected)ᶜ)) : X) = z.1
    dsimp only [a]
    rw [Equiv.apply_symm_apply]
    exact hh

@[simp] theorem orbitEquiv_val
    (o : OrbitProfileFromOrbits.Orbit (image H selected eC)) (a : o.orbit) :
    ((orbitEquiv H selected eC o a :
        (ambientOrbit H selected eC o).orbit) : X) =
      ((eC a.1 : ↥((orbitSubaction H selected)ᶜ)) : X) := rfl

/-- Restriction to corresponding complement and ambient orbits is conjugate
for every actual original element. -/
theorem orbitEquiv_action
    (o : OrbitProfileFromOrbits.Orbit (image H selected eC)) (h : H) :
    (orbitEquiv H selected eC o).permCongr
        (MulAction.toPermHom (image H selected eC) o.orbit
          ⟨secondHom H selected eC h, ⟨h, rfl⟩⟩) =
      MulAction.toPermHom H (ambientOrbit H selected eC o).orbit h := by
  apply Equiv.ext
  intro z
  obtain ⟨a, rfl⟩ := (orbitEquiv H selected eC o).surjective z
  apply Subtype.ext
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  change ((eC (eC.symm
      ⟨(h : Equiv.Perm X)
        ((eC a.1 : ↥((orbitSubaction H selected)ᶜ)) : X), _⟩) :
        ↥((orbitSubaction H selected)ᶜ)) : X) =
    (h : Equiv.Perm X)
      ((eC a.1 : ↥((orbitSubaction H selected)ᶜ)) : X)
  rw [Equiv.apply_symm_apply]

/-- The complete induced action image on a complement orbit is exactly its
original ambient action image, after the literal point equivalence. -/
theorem relabel_orbitImage
    (o : OrbitProfileFromOrbits.Orbit (image H selected eC)) :
    relabelSubgroup (orbitEquiv H selected eC o)
        (OrbitProfileFromOrbits.orbitImage (image H selected eC) o) =
      OrbitProfileFromOrbits.orbitImage H (ambientOrbit H selected eC o) := by
  ext v
  constructor
  · intro hv
    rw [mem_relabelSubgroup] at hv
    obtain ⟨g, hg⟩ := hv
    obtain ⟨h, hh⟩ := g.property
    let h' : H := h
    refine ⟨h', ?_⟩
    have hge : g =
        (⟨secondHom H selected eC h', ⟨h', rfl⟩⟩ :
          image H selected eC) := Subtype.ext hh.symm
    subst g
    rw [← orbitEquiv_action H selected eC o h']
    rw [hg]
    exact ((orbitEquiv H selected eC o).permCongr).apply_symm_apply v
  · rintro ⟨h, rfl⟩
    apply (mem_relabelSubgroup (orbitEquiv H selected eC o)
      (OrbitProfileFromOrbits.orbitImage (image H selected eC) o) _).mpr
    let g : image H selected eC :=
      ⟨secondHom H selected eC h, ⟨h, rfl⟩⟩
    refine ⟨g, ?_⟩
    apply ((orbitEquiv H selected eC o).permCongr).injective
    rw [orbitEquiv_action H selected eC o h]
    exact (((orbitEquiv H selected eC o).permCongr).apply_symm_apply _).symm

/-- Different complement-image orbits remain different original orbits. -/
theorem ambientOrbit_injective :
    Function.Injective (ambientOrbit H selected eC) := by
  intro o p hop
  have hp : ((eC p.out : ↥((orbitSubaction H selected)ᶜ)) : X) ∈
      (ambientOrbit H selected eC o).orbit := by
    rw [hop]
    exact (orbitEquiv H selected eC p ⟨p.out, by
      rw [p.orbit_eq_orbit_out Quotient.out_eq']
      exact MulAction.mem_orbit_self p.out⟩).property
  obtain ⟨h, hh⟩ := by
    rw [ambientOrbit, MulAction.orbitRel.Quotient.orbit_mk] at hp
    exact hp
  let g : image H selected eC :=
    ⟨secondHom H selected eC h, ⟨h, rfl⟩⟩
  have hq : Quotient.mk'' p.out = o :=
    (MulAction.orbitRel.Quotient.mem_orbit).mp (by
      rw [o.orbit_eq_orbit_out Quotient.out_eq']
      exact ⟨g, by
        change eC.symm
            ⟨(h : Equiv.Perm X)
                ((eC o.out : ↥((orbitSubaction H selected)ᶜ)) : X), _⟩ = p.out
        apply eC.injective
        apply Subtype.ext
        simpa only [Equiv.apply_symm_apply] using hh⟩)
  exact hq.symm.trans (Quotient.out_eq' p)

/-- The second projection of the actual deleted fusion model is exactly the
literal action image on the complement.  Thus a source condition proved on
the complement is attached to the model consumed by the fusion count, with
no enlargement or independently chosen source. -/
theorem deletedSource_eq_image
    (U : Subgroup (Equiv.Perm Ω))
    (himage : relabelSubgroup eO U =
      OrbitProfileFromOrbits.orbitImage H selected) :
    (fusionDeletedModel U
        (relabelSubgroup (chart H selected eO eC).symm H)).map
          (MonoidHom.snd U (Equiv.Perm Z)) =
      image H selected eC := by
  let K : Subgroup (Equiv.Perm (Ω ⊕ Z)) :=
    relabelSubgroup (chart H selected eO eC).symm H
  have hprojection :
      (fusionPhysicalBlockPullback K).map
          (MonoidHom.fst (Equiv.Perm Ω) (Equiv.Perm Z)) = U :=
    chart_projection_eq H selected U eO eC himage
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hpair : ((p.1 : Equiv.Perm Ω), p.2) ∈
        fusionPhysicalBlockPullback K := hp
    rw [blockPullback_eq_range H selected eO eC] at hpair
    obtain ⟨h, hh⟩ := hpair
    exact ⟨h, congrArg Prod.snd hh⟩
  · rintro ⟨h, rfl⟩
    have hpair : pairHom H selected eO eC h ∈
        fusionPhysicalBlockPullback K := by
      rw [blockPullback_eq_range H selected eO eC]
      exact ⟨h, rfl⟩
    have hfirst : firstHom H selected eO h ∈ U := by
      rw [← hprojection]
      exact ⟨pairHom H selected eO eC h, hpair, rfl⟩
    let u : U := ⟨firstHom H selected eO h, hfirst⟩
    refine ⟨(u, secondHom H selected eC h), ?_, rfl⟩
    exact hpair

end Complement
end SymmetricSubgroupAsymptotics.FusionOrbitProfileChart

end
