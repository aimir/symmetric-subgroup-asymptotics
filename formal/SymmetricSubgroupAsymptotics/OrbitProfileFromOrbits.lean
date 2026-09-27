import SymmetricSubgroupAsymptotics.OrbitProfileAssembly
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# A full original profile from simultaneous actual orbit charts

Each literal orbit of the same original subgroup receives an action label
and a point chart identifying its actual action image with that action.
The label fibres determine the multiplicities. Regrouping the literal orbit
decomposition produces one full profile on the original point set.

No subgroup-count premise, enumeration, product decomposition of the group,
or action-separation premise is needed for this structural construction.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.OrbitProfileFromOrbits

variable {X ι : Type*} {Ω : ι → Type*}
    (H : Subgroup (Equiv.Perm X)) (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))

abbrev Orbit := MulAction.orbitRel.Quotient H X

/-- The literal restriction image of H on this original orbit. -/
def orbitImage (o : Orbit H) : Subgroup (Equiv.Perm o.orbit) :=
  (MulAction.toPermHom H o.orbit).range

/-- Point charts of the actual orbit images, using one common label type.
Labels may repeat; their actual fibres become the profile occurrences. -/
structure Data where
  label : Orbit H → ι
  pointEquiv : ∀ o : Orbit H, Ω (label o) ≃ o.orbit
  image_eq : ∀ o : Orbit H,
    relabelSubgroup (pointEquiv o) (U (label o)) = orbitImage H o

namespace Data

variable {H U} (C : Data H U)

abbrev Fiber (i : ι) := {o : Orbit H // C.label o = i}

/-- The chart of a labelled orbit with the equality of labels retained. -/
def fiberChart (i : ι) (o : C.Fiber i) : Ω i ≃ o.1.orbit := by
  rcases o with ⟨o,rfl⟩
  exact C.pointEquiv o

theorem fiberChart_image (i : ι) (o : C.Fiber i) :
    relabelSubgroup (C.fiberChart i o) (U i) = orbitImage H o.1 := by
  rcases o with ⟨o,rfl⟩
  exact C.image_eq o

variable [Finite X]

instance fiberFintype (i : ι) : Fintype (C.Fiber i) := Fintype.ofFinite _

/-- The number of actual original orbits having this action label. -/
def multiplicity (i : ι) : ℕ := Fintype.card (C.Fiber i)

def occurrence (i : ι) : Fin (C.multiplicity i) ≃ C.Fiber i :=
  (Fintype.equivFin _).symm

/-- Each original orbit occurs once, including across repeated labels. -/
def orbitIndex : (Σ i, Fin (C.multiplicity i)) ≃ Orbit H :=
  (Equiv.sigmaCongrRight (fun i => C.occurrence i)).trans
    (Equiv.sigmaFiberEquiv C.label)

def localChart (i : ι) (j : Fin (C.multiplicity i)) :
    Ω i ≃ (C.orbitIndex ⟨i,j⟩).orbit :=
  C.fiberChart i (C.occurrence i j)

theorem localChart_image (i : ι) (j : Fin (C.multiplicity i)) :
    relabelSubgroup (C.localChart i j) (U i) = orbitImage H (C.orbitIndex ⟨i,j⟩) :=
  C.fiberChart_image i (C.occurrence i j)

private def toOrbits (z : OrbitProfilePoints Ω C.multiplicity) :
    Σ o : Orbit H, o.orbit :=
  ⟨C.orbitIndex ⟨z.1,z.2.1⟩, C.localChart z.1 z.2.1 z.2.2⟩

private theorem toOrbits_bijective : Function.Bijective C.toOrbits := by
  constructor
  · rintro ⟨i,j,x⟩ ⟨i',j',x'⟩ h
    have hij : (⟨i,j⟩ : Σ i, Fin (C.multiplicity i)) = ⟨i',j'⟩ :=
      C.orbitIndex.injective (congrArg Sigma.fst h)
    obtain rfl : i = i' := (Sigma.mk.inj_iff.mp hij).1
    obtain rfl : j = j' := eq_of_heq (Sigma.mk.inj_iff.mp hij).2
    change (⟨C.orbitIndex ⟨i,j⟩,C.localChart i j x⟩ : Σ o : Orbit H, o.orbit) =
      ⟨C.orbitIndex ⟨i,j⟩,C.localChart i j x'⟩ at h
    have hx : C.localChart i j x = C.localChart i j x' :=
      eq_of_heq (Sigma.mk.inj_iff.mp h).2
    exact congrArg (fun y => (⟨i,j,y⟩ : OrbitProfilePoints Ω C.multiplicity))
      ((C.localChart i j).injective hx)
  · rintro ⟨o,x⟩
    obtain ⟨⟨i,j⟩,rfl⟩ := C.orbitIndex.surjective o
    refine ⟨⟨i,j,(C.localChart i j).symm x⟩,?_⟩
    change (⟨C.orbitIndex ⟨i,j⟩,
      C.localChart i j ((C.localChart i j).symm x)⟩ : Σ o : Orbit H, o.orbit) = _
    rw [Equiv.apply_symm_apply]

/-- The simultaneous chart into the same original point set, obtained
from the literal disjoint orbit decomposition. -/
def chart : OrbitProfilePoints Ω C.multiplicity ≃ X :=
  (Equiv.ofBijective C.toOrbits C.toOrbits_bijective).trans
    (MulAction.selfEquivSigmaOrbits' H X).symm

@[simp] theorem chart_apply (i : ι) (j : Fin (C.multiplicity i)) (x : Ω i) :
    C.chart ⟨i,j,x⟩ = (C.localChart i j x : X) := rfl

/-- Every displayed profile block is exactly its original orbit. -/
theorem chart_block (i : ι) (j : Fin (C.multiplicity i)) :
    Set.range (fun x : Ω i => C.chart ⟨i,j,x⟩) = (C.orbitIndex ⟨i,j⟩).orbit := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact (C.localChart i j y).property
  · intro hx
    refine ⟨(C.localChart i j).symm ⟨x,hx⟩,?_⟩
    change ((C.localChart i j) ((C.localChart i j).symm ⟨x,hx⟩) : X) = x
    rw [Equiv.apply_symm_apply]

private theorem local_maps (i : ι) (j : Fin (C.multiplicity i)) (h : H) :
    ∃ u : U i, ∀ x : Ω i,
      (h : Equiv.Perm X) (C.localChart i j x : X) =
        (C.localChart i j ((u : Equiv.Perm (Ω i)) x) : X) := by
  let e := C.localChart i j
  let a := MulAction.toPermHom H (C.orbitIndex ⟨i,j⟩).orbit h
  have ha : a ∈ orbitImage H (C.orbitIndex ⟨i,j⟩) := ⟨h,rfl⟩
  have he : relabelSubgroup e (U i) = orbitImage H (C.orbitIndex ⟨i,j⟩) :=
    C.localChart_image i j
  have hu : e.symm.permCongr a ∈ U i := by
    apply (mem_relabelSubgroup e (U i) a).mp
    rw [he]
    exact ha
  refine ⟨⟨e.symm.permCongr a,hu⟩,fun x => ?_⟩
  change (a (e x) : X) = (e (e.symm (a (e x))) : X)
  rw [Equiv.apply_symm_apply]

private theorem local_full (i : ι) (j : Fin (C.multiplicity i)) (u : U i) :
    ∃ h : H, ∀ x : Ω i,
      (h : Equiv.Perm X) (C.localChart i j x : X) =
        (C.localChart i j ((u : Equiv.Perm (Ω i)) x) : X) := by
  let e := C.localChart i j
  have he : relabelSubgroup e (U i) = orbitImage H (C.orbitIndex ⟨i,j⟩) :=
    C.localChart_image i j
  have hu : e.permCongr (u : Equiv.Perm (Ω i)) ∈ orbitImage H (C.orbitIndex ⟨i,j⟩) := by
    rw [← he]
    apply (mem_relabelSubgroup e (U i) _).mpr
    change e.permCongr.symm (e.permCongr (u : Equiv.Perm (Ω i))) ∈ U i
    rw [Equiv.symm_apply_apply]
    exact u.property
  obtain ⟨h,hh⟩ := hu
  refine ⟨h,fun x => ?_⟩
  have hx := congrArg Subtype.val (Equiv.congr_fun hh (e x))
  simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using hx

/-- Fullness is derived from the exact original restriction images. The
same H supplies every coordinate map and every fullness witness. -/
theorem chart_full : OrbitProfileFullOn U C.chart H := by
  constructor
  · intro h i j
    simpa only [chart_apply] using C.local_maps i j h
  · intro i j u
    simpa only [chart_apply] using C.local_full i j u

include C in
theorem exists_profile :
    ∃ m : ι → ℕ, ∃ e : OrbitProfilePoints Ω m ≃ X, OrbitProfileFullOn U e H :=
  ⟨C.multiplicity,C.chart,C.chart_full⟩

end Data

/-- Pointwise actual action coverage is enough to assemble every orbit
simultaneously. This does not assume any cardinality or profile bound. -/
theorem exists_profile_of_orbit_charts [Finite X]
    (hcover : ∀ o : Orbit H, ∃ i : ι, ∃ e : Ω i ≃ o.orbit,
      relabelSubgroup e (U i) = orbitImage H o) :
    ∃ m : ι → ℕ, ∃ e : OrbitProfilePoints Ω m ≃ X, OrbitProfileFullOn U e H := by
  choose label pointEquiv himage using hcover
  let C : Data H U := ⟨label,pointEquiv,himage⟩
  exact C.exists_profile

end SymmetricSubgroupAsymptotics.OrbitProfileFromOrbits

end
