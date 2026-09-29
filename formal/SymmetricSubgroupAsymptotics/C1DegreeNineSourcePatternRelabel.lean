import SymmetricSubgroupAsymptotics.C1DegreeNineSourceRank
import SymmetricSubgroupAsymptotics.TernaryHighOwnerCapacity

/-!
# Relabelling invariance of the exact c=1 source pattern

A bijection of points carries every literal orbit of a permutation subgroup
to a literal orbit of its relabelled subgroup, and the two actual orbit
images are identified by the restricted point bijection.  Consequently the
unique-regular-`C3`, no-natural-`A4` source pattern is a property of the
permutation-conjugacy class of the complete physical subgroup.  No orbit is
chosen, and no abstract group isomorphism replaces the literal action.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace OrbitProfileFromOrbits

variable {X Y : Type} (e : X ≃ Y) (G : Subgroup (Equiv.Perm X))

/-- The orbit of the relabelled subgroup through the image of a literal
representative of an original orbit. -/
def relabelOrbit (o : Orbit G) : Orbit (relabelSubgroup e G) :=
  Quotient.mk'' (e o.out)

theorem mem_relabelOrbit_orbit (o : Orbit G) (y : Y) :
    y ∈ (relabelOrbit e G o).orbit ↔ e.symm y ∈ o.orbit := by
  have ho : o.orbit = MulAction.orbit G o.out := by
    rw [← MulAction.orbitRel.Quotient.orbit_mk, Quotient.out_eq']
  rw [ho, relabelOrbit, MulAction.orbitRel.Quotient.orbit_mk]
  constructor
  · rintro ⟨g, rfl⟩
    have hg : e.symm.permCongr (g : Equiv.Perm Y) ∈ G :=
      (mem_relabelSubgroup e G g).mp g.2
    refine ⟨⟨_, hg⟩, ?_⟩
    change e.symm ((g : Equiv.Perm Y) (e o.out)) =
      e.symm ((g : Equiv.Perm Y) (e o.out))
    rfl
  · rintro ⟨h, hh⟩
    have hmem : e.permCongr (h : Equiv.Perm X) ∈ relabelSubgroup e G := by
      rw [mem_relabelSubgroup]
      have hid : e.symm.permCongr (e.permCongr (h : Equiv.Perm X)) =
          (h : Equiv.Perm X) := by
        apply Equiv.ext
        intro x
        simp [Equiv.permCongr_apply]
      rw [hid]
      exact h.2
    refine ⟨⟨_, hmem⟩, ?_⟩
    change e ((h : Equiv.Perm X) (e.symm (e o.out))) = y
    rw [e.symm_apply_apply]
    change (h : Equiv.Perm X) o.out = e.symm y at hh
    rw [hh, e.apply_symm_apply]

/-- The literal point bijection between an orbit and its relabelled orbit. -/
def relabelOrbitEquiv (o : Orbit G) : o.orbit ≃ (relabelOrbit e G o).orbit :=
  e.subtypeEquiv fun x => by
    rw [mem_relabelOrbit_orbit, e.symm_apply_apply]

@[simp] theorem relabelOrbitEquiv_apply (o : Orbit G) (x : o.orbit) :
    ((relabelOrbitEquiv e G o x : (relabelOrbit e G o).orbit) : Y) = e x :=
  rfl

/-- The actual image on the relabelled orbit is the relabelled actual image
on the original orbit. -/
theorem relabel_orbitImage_relabelOrbit (o : Orbit G) :
    relabelSubgroup (relabelOrbitEquiv e G o) (orbitImage G o) =
      orbitImage (relabelSubgroup e G) (relabelOrbit e G o) := by
  let eo := relabelOrbitEquiv e G o
  have hmem : ∀ h : G, e.permCongr (h : Equiv.Perm X) ∈ relabelSubgroup e G := by
    intro h
    rw [mem_relabelSubgroup]
    have hid : e.symm.permCongr (e.permCongr (h : Equiv.Perm X)) =
        (h : Equiv.Perm X) := by
      apply Equiv.ext
      intro x
      simp [Equiv.permCongr_apply]
    rw [hid]
    exact h.2
  ext p
  constructor
  · intro hp
    rw [mem_relabelSubgroup] at hp
    obtain ⟨h, hh⟩ := hp
    refine ⟨⟨_, hmem h⟩, ?_⟩
    apply Equiv.ext
    intro z
    obtain ⟨x, rfl⟩ := eo.surjective z
    apply Subtype.ext
    have hx : (eo.symm.permCongr p) x = MulAction.toPermHom G o.orbit h x := by
      rw [hh]
    have hpx : p (eo x) = eo ((eo.symm.permCongr p) x) := by
      simp [Equiv.permCongr_apply]
    rw [hpx, hx]
    change e ((h : Equiv.Perm X) (e.symm (e x))) = e ((h : Equiv.Perm X) x)
    rw [e.symm_apply_apply]
  · rintro ⟨g, rfl⟩
    rw [mem_relabelSubgroup]
    have hg : e.symm.permCongr (g : Equiv.Perm Y) ∈ G :=
      (mem_relabelSubgroup e G g).mp g.2
    refine ⟨⟨_, hg⟩, ?_⟩
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rfl

theorem relabelOrbit_surjective :
    Function.Surjective (relabelOrbit e G) := by
  intro o'
  refine ⟨Quotient.mk'' (e.symm o'.out), ?_⟩
  have hx : o'.out ∈ o'.orbit :=
    (MulAction.orbitRel.Quotient.mem_orbit).mpr (Quotient.out_eq' o')
  have hy : o'.out ∈ (relabelOrbit e G (Quotient.mk'' (e.symm o'.out))).orbit := by
    rw [mem_relabelOrbit_orbit]
    exact (MulAction.orbitRel.Quotient.mem_orbit).mpr rfl
  exact ((MulAction.orbitRel.Quotient.mem_orbit).mp hy).symm.trans
    ((MulAction.orbitRel.Quotient.mem_orbit).mp hx)

theorem relabelOrbit_injective :
    Function.Injective (relabelOrbit e G) := by
  intro o₁ o₂ h
  have hx₁ : o₁.out ∈ o₁.orbit :=
    (MulAction.orbitRel.Quotient.mem_orbit).mpr (Quotient.out_eq' o₁)
  have hy : e o₁.out ∈ (relabelOrbit e G o₂).orbit := by
    rw [← h, mem_relabelOrbit_orbit, e.symm_apply_apply]
    exact hx₁
  rw [mem_relabelOrbit_orbit, e.symm_apply_apply] at hy
  exact ((MulAction.orbitRel.Quotient.mem_orbit).mp hx₁).symm.trans
    ((MulAction.orbitRel.Quotient.mem_orbit).mp hy)

end OrbitProfileFromOrbits

open OrbitProfileFromOrbits

variable {X Y : Type}

/-- Regularity of a literal degree-three `C3` orbit is unchanged by
relabelling the points. -/
theorem isRegularC3Orbit_relabelOrbit_iff (e : X ≃ Y)
    (G : Subgroup (Equiv.Perm X)) (o : Orbit G) :
    IsRegularC3Orbit (relabelSubgroup e G) (relabelOrbit e G o) ↔
      IsRegularC3Orbit G o := by
  let eo := relabelOrbitEquiv e G o
  have himage := relabel_orbitImage_relabelOrbit e G o
  let g : orbitImage G o ≃*
      orbitImage (relabelSubgroup e G) (relabelOrbit e G o) :=
    (eo.permCongrHom.subgroupMap (orbitImage G o)).trans
      (MulEquiv.subgroupCongr himage)
  constructor
  · rintro ⟨hcard, hp⟩
    exact ⟨(Nat.card_congr eo).trans hcard, hp.of_equiv g.symm⟩
  · rintro ⟨hcard, hp⟩
    exact ⟨(Nat.card_congr eo).symm.trans hcard, hp.of_equiv g⟩

/-- A natural `A4` action on a relabelled orbit is already natural on the
original orbit, with the same literal point chart up to relabelling. -/
theorem isNaturalA4Action_relabelOrbit_iff (e : X ≃ Y)
    (G : Subgroup (Equiv.Perm X)) (o : Orbit G) :
    IsNaturalA4Action
        (orbitImage (relabelSubgroup e G) (relabelOrbit e G o))
        (relabelOrbit e G o).orbit ↔
      IsNaturalA4Action (orbitImage G o) o.orbit := by
  let eo := relabelOrbitEquiv e G o
  have himage := relabel_orbitImage_relabelOrbit e G o
  constructor
  · intro h
    rw [← himage] at h
    have h' := TernaryHighEarlierOwner.naturalA4_relabel eo.symm
      (relabelSubgroup eo (orbitImage G o)) h
    rwa [relabelSubgroup_symm] at h'
  · intro h
    rw [← himage]
    exact TernaryHighEarlierOwner.naturalA4_relabel eo (orbitImage G o) h

/-- The exact c=1 source pattern is carried forward by any relabelling. -/
theorem C1DegreeNineSourcePattern.relabel (e : X ≃ Y)
    {G : Subgroup (Equiv.Perm X)} (h : C1DegreeNineSourcePattern G) :
    C1DegreeNineSourcePattern (relabelSubgroup e G) := by
  obtain ⟨exceptional, hregular, hunique, hnoA4⟩ := h
  refine ⟨relabelOrbit e G exceptional,
    (isRegularC3Orbit_relabelOrbit_iff e G exceptional).mpr hregular,
    ?_, ?_⟩
  · intro o' ho'
    obtain ⟨o, rfl⟩ := relabelOrbit_surjective e G o'
    rw [hunique o ((isRegularC3Orbit_relabelOrbit_iff e G o).mp ho')]
  · intro o' ho'
    obtain ⟨o, rfl⟩ := relabelOrbit_surjective e G o'
    exact hnoA4 o ((isNaturalA4Action_relabelOrbit_iff e G o).mp ho')

/-- The exact c=1 source pattern is a relabelling invariant. -/
theorem c1DegreeNineSourcePattern_relabel_iff (e : X ≃ Y)
    (G : Subgroup (Equiv.Perm X)) :
    C1DegreeNineSourcePattern (relabelSubgroup e G) ↔
      C1DegreeNineSourcePattern G := by
  constructor
  · intro h
    simpa only [relabelSubgroup_symm] using h.relabel e.symm
  · exact C1DegreeNineSourcePattern.relabel e

end SymmetricSubgroupAsymptotics

end
