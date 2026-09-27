import SymmetricSubgroupAsymptotics.SingletonExtension
import SymmetricSubgroupAsymptotics.OrbitProfileFromOrbits

/-!
# Literal moving orbits under a singleton extension

Adding one fixed point changes neither an original orbit nor its full
permutation image.  The statements here retain the original subgroup and
the actual point chart, so they can be used before any profile assembly.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SingletonExtension

variable {α X : Type*}

def extendedOrbit (e : X ≃ Option α) (H : Subgroup (Equiv.Perm α))
    (o : OrbitProfileFromOrbits.Orbit H) :
    OrbitProfileFromOrbits.Orbit (H.map (extensionHom e)) :=
  Quotient.mk'' (e.symm (some o.out))

/-- The original orbit is literally the corresponding moving orbit after
the singleton has been added. -/
def orbitEquiv (e : X ≃ Option α) (H : Subgroup (Equiv.Perm α))
    (o : OrbitProfileFromOrbits.Orbit H) :
    o.orbit ≃ (extendedOrbit e H o).orbit := by
  let f : o.orbit → (extendedOrbit e H o).orbit := fun a =>
    ⟨e.symm (some a.1), by
      rw [extendedOrbit, MulAction.orbitRel.Quotient.orbit_mk]
      have ha : a.1 ∈ MulAction.orbit H o.out := by
        rw [← o.orbit_eq_orbit_out Quotient.out_eq']
        exact a.property
      obtain ⟨g,hg⟩ := ha
      refine ⟨⟨extensionHom e g, Subgroup.mem_map.mpr ⟨g,g.property,rfl⟩⟩, ?_⟩
      change extensionHom e g (e.symm (some o.out)) = e.symm (some a.1)
      rw [extensionHom_some]
      exact congrArg e.symm (congrArg some hg)
    ⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro a b hab
    apply Subtype.ext
    apply Option.some_injective
    apply e.symm.injective
    exact congrArg Subtype.val hab
  · intro z
    have hz : z.1 ∈ MulAction.orbit (H.map (extensionHom e))
        (e.symm (some o.out)) := by
      rw [← MulAction.orbitRel.Quotient.orbit_mk]
      exact z.property
    obtain ⟨k,hk⟩ := hz
    obtain ⟨g,hg,hgk⟩ := Subgroup.mem_map.mp k.property
    let a : o.orbit := ⟨g o.out, by
      rw [o.orbit_eq_orbit_out Quotient.out_eq']
      exact ⟨⟨g,hg⟩,rfl⟩⟩
    refine ⟨a,Subtype.ext ?_⟩
    change e.symm (some (g o.out)) = z.1
    have hk' : extensionHom e g (e.symm (some o.out)) = z.1 := by
      change (k : Equiv.Perm X) (e.symm (some o.out)) = z.1 at hk
      rw [← hgk] at hk
      exact hk
    rw [extensionHom_some] at hk'
    exact hk'

theorem orbitEquiv_apply (e : X ≃ Option α) (H : Subgroup (Equiv.Perm α))
    (o : OrbitProfileFromOrbits.Orbit H) (a : o.orbit) :
    ((orbitEquiv e H o a : (extendedOrbit e H o).orbit) : X) =
      e.symm (some a.1) := rfl

/-- Restricting an extended element to the corresponding moving orbit is
conjugate to the original restriction by `orbitEquiv`. -/
theorem orbitEquiv_action (e : X ≃ Option α) (H : Subgroup (Equiv.Perm α))
    (o : OrbitProfileFromOrbits.Orbit H) (g : H) :
    (orbitEquiv e H o).permCongr
        (MulAction.toPermHom H o.orbit g) =
      MulAction.toPermHom (H.map (extensionHom e)) (extendedOrbit e H o).orbit
        ⟨extensionHom e g.1,Subgroup.mem_map.mpr ⟨g.1,g.2,rfl⟩⟩ := by
  apply Equiv.ext
  intro z
  obtain ⟨a,rfl⟩ := (orbitEquiv e H o).surjective z
  apply Subtype.ext
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
  change e.symm (some ((g : Equiv.Perm α) a.1)) =
    extensionHom e g.1 (e.symm (some a.1))
  rw [extensionHom_some]

/-- The complete permutation image on each moving orbit is retained, not
merely its abstract isomorphism type or cardinality. -/
theorem relabel_orbitImage (e : X ≃ Option α)
    (H : Subgroup (Equiv.Perm α)) (o : OrbitProfileFromOrbits.Orbit H) :
    relabelSubgroup (orbitEquiv e H o)
        (OrbitProfileFromOrbits.orbitImage H o) =
      OrbitProfileFromOrbits.orbitImage (H.map (extensionHom e))
        (extendedOrbit e H o) := by
  ext v
  constructor
  · intro hv
    rw [mem_relabelSubgroup] at hv
    obtain ⟨g,hg⟩ := hv
    refine ⟨⟨extensionHom e g.1,Subgroup.mem_map.mpr ⟨g.1,g.2,rfl⟩⟩,?_⟩
    rw [← orbitEquiv_action e H o g]
    rw [hg]
    exact ((orbitEquiv e H o).permCongr).apply_symm_apply v
  · rintro ⟨k,rfl⟩
    obtain ⟨g,hg,hgk⟩ := Subgroup.mem_map.mp k.property
    have hk : k =
        (⟨extensionHom e g,Subgroup.mem_map.mpr ⟨g,hg,rfl⟩⟩ :
          H.map (extensionHom e)) := Subtype.ext hgk.symm
    subst k
    apply (mem_relabelSubgroup (orbitEquiv e H o)
      (OrbitProfileFromOrbits.orbitImage H o) _).mpr
    refine ⟨⟨g,hg⟩,?_⟩
    apply ((orbitEquiv e H o).permCongr).injective
    rw [orbitEquiv_action]
    exact (((orbitEquiv e H o).permCongr).apply_symm_apply _).symm

end SymmetricSubgroupAsymptotics.SingletonExtension

end
