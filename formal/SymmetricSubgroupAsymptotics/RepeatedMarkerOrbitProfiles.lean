import SymmetricSubgroupAsymptotics.BinaryExteriorOrbitMenu
import SymmetricSubgroupAsymptotics.SmallOriginalOrbitCharts

/-!
# Original mixed binary and full-S3 orbits in the complete marker profile

Every original orbit is required to have either binary image or the full
original three-point symmetric action. This is an explicit local structural
condition, not a claim about arbitrary odd actions. The same original H is
profiled, and singleton/marker multiplicities equal its literal orbit counts.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerOrbitProfiles

abbrev Color (n : ℕ) := PUnit.{1} ⊕ (PUnit.{1} ⊕ (PUnit.{1} ⊕ BinaryExteriorOrbitMenu.Label n))
abbrev points (n : ℕ) := RepeatedMarkerCompleteProfile.points (BinaryExteriorOrbitMenu.points n)
abbrev action (n : ℕ) := RepeatedMarkerCompleteProfile.action
  (BinaryExteriorOrbitMenu.points n) (BinaryExteriorOrbitMenu.action n)

def fixedLabel (n : ℕ) : Color n := .inl PUnit.unit
def markerLabel (n : ℕ) : Color n := .inr (.inl PUnit.unit)
def pairLabel (n : ℕ) : Color n := .inr (.inr (.inl PUnit.unit))
def exteriorLabel {n : ℕ} (i : BinaryExteriorOrbitMenu.Label n) : Color n :=
  .inr (.inr (.inr i))

@[simp] theorem fixed_point_card (n : ℕ) : Nat.card (points n (fixedLabel n)) = 1 := by
  change Nat.card PUnit.{1} = 1
  simp

@[simp] theorem marker_point_card (n : ℕ) : Nat.card (points n (markerLabel n)) = 3 := by
  change Nat.card (Fin 3) = 3
  simp

@[simp] theorem pair_point_card (n : ℕ) : Nat.card (points n (pairLabel n)) = 2 := by
  change Nat.card (criticalActionPoints .c2) = 2
  rw [Nat.card_eq_fintype_card,criticalAction_point_card]
  rfl

@[simp] theorem exterior_point_card (n : ℕ) (i : BinaryExteriorOrbitMenu.Label n) :
    Nat.card (points n (exteriorLabel i)) = Nat.card (BinaryExteriorOrbitMenu.points n i) := rfl

theorem point_card_eq_one_iff (n : ℕ) (i : Color n) :
    Nat.card (points n i) = 1 ↔ i = fixedLabel n := by
  rcases i with a | (a | (a | i))
  · cases a
    change Nat.card (points n (fixedLabel n)) = 1 ↔ fixedLabel n = fixedLabel n
    exact ⟨fun _ => rfl,fun _ => fixed_point_card n⟩
  · cases a
    change Nat.card (points n (markerLabel n)) = 1 ↔ _
    constructor
    · intro h
      exact False.elim ((by decide : (3 : ℕ) ≠ 1) ((marker_point_card n).symm.trans h))
    · intro h
      change (.inr (.inl PUnit.unit) : Color n) = .inl PUnit.unit at h
      cases h
  · cases a
    change Nat.card (points n (pairLabel n)) = 1 ↔ _
    constructor
    · intro h
      exact False.elim ((by decide : (2 : ℕ) ≠ 1) ((pair_point_card n).symm.trans h))
    · intro h
      change (.inr (.inr (.inl PUnit.unit)) : Color n) = .inl PUnit.unit at h
      cases h
  · have hi : Nat.card (BinaryExteriorOrbitMenu.points n i) ≠ 1 := by
      rw [Nat.card_eq_fintype_card]
      exact BinaryExteriorOrbitMenu.point_card_ne_one n i
    change Nat.card (points n (exteriorLabel i)) = 1 ↔ _
    constructor
    · intro h
      exact False.elim (hi h)
    · intro h
      change (.inr (.inr (.inr i)) : Color n) = .inl PUnit.unit at h
      cases h

theorem point_card_eq_three_iff (n : ℕ) (i : Color n) :
    Nat.card (points n i) = 3 ↔ i = markerLabel n := by
  rcases i with a | (a | (a | i))
  · cases a
    change Nat.card (points n (fixedLabel n)) = 3 ↔ _
    constructor
    · intro h
      exact False.elim ((by decide : (1 : ℕ) ≠ 3) ((fixed_point_card n).symm.trans h))
    · intro h
      change (.inl PUnit.unit : Color n) = .inr (.inl PUnit.unit) at h
      cases h
  · cases a
    change Nat.card (points n (markerLabel n)) = 3 ↔ markerLabel n = markerLabel n
    exact ⟨fun _ => rfl,fun _ => marker_point_card n⟩
  · cases a
    change Nat.card (points n (pairLabel n)) = 3 ↔ _
    constructor
    · intro h
      exact False.elim ((by decide : (2 : ℕ) ≠ 3) ((pair_point_card n).symm.trans h))
    · intro h
      change (.inr (.inr (.inl PUnit.unit)) : Color n) = .inr (.inl PUnit.unit) at h
      cases h
  · have hi : Nat.card (BinaryExteriorOrbitMenu.points n i) ≠ 3 := by
      rw [Nat.card_eq_fintype_card]
      exact RepeatedOddMarkerPhysicalBinary.exteriorDegree_ne_three
        (BinaryExteriorOrbitMenu.points n) (BinaryExteriorOrbitMenu.action n)
        (BinaryExteriorOrbitMenu.action_isPGroup n) (BinaryExteriorOrbitMenu.action_transitive n) i
    change Nat.card (points n (exteriorLabel i)) = 3 ↔ _
    constructor
    · intro h
      exact False.elim (hi h)
    · intro h
      change (.inr (.inr (.inr i)) : Color n) = .inr (.inl PUnit.unit) at h
      cases h

variable {X : Type} [Fintype X] (H : Subgroup (Equiv.Perm X))

/-- Binary images or the actual full S3 action on the same orbit. -/
def Fits : Prop := ∀ o : OrbitProfileFromOrbits.Orbit H,
  IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H o) ∨
    ∃ e : Fin 3 ≃ o.orbit,
      relabelSubgroup e oddMarkerActionSubgroup = OrbitProfileFromOrbits.orbitImage H o

/-- Count original orbit subsets, not chosen points or point charts. -/
def orbitCount (d : ℕ) : ℕ :=
  Nat.card {o : OrbitProfileFromOrbits.Orbit H // Nat.card o.orbit = d}

theorem orbit_cover (n : ℕ) (hdegree : Fintype.card X ≤ n) (hfits : Fits H)
    (o : OrbitProfileFromOrbits.Orbit H) :
    ∃ i : Color n, ∃ e : points n i ≃ o.orbit,
      relabelSubgroup e (action n i) = OrbitProfileFromOrbits.orbitImage H o := by
  by_cases h1 : Nat.card o.orbit = 1
  · obtain ⟨e,he⟩ := SmallOriginalOrbitCharts.singleton_chart H o h1
    exact ⟨fixedLabel n,e,he⟩
  by_cases h2 : Nat.card o.orbit = 2
  · obtain ⟨e,he⟩ := SmallOriginalOrbitCharts.pair_chart H o h2
    exact ⟨pairLabel n,e,he⟩
  rcases hfits o with hb | ⟨e,he⟩
  · obtain ⟨i,e,he⟩ := BinaryExteriorOrbitMenu.orbit_cover H n hdegree o hb h1 h2
    exact ⟨exteriorLabel i,e,he⟩
  · exact ⟨markerLabel n,e,he⟩

theorem multiplicity_fixed (n : ℕ) (C : OrbitProfileFromOrbits.Data H (action n)) :
    C.multiplicity (fixedLabel n) = orbitCount H 1 := by
  change Fintype.card (C.Fiber (fixedLabel n)) = _
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro o
  change C.label o = fixedLabel n ↔ Nat.card o.orbit = 1
  rw [← Nat.card_congr (C.pointEquiv o)]
  exact (point_card_eq_one_iff n (C.label o)).symm

theorem multiplicity_marker (n : ℕ) (C : OrbitProfileFromOrbits.Data H (action n)) :
    C.multiplicity (markerLabel n) = orbitCount H 3 := by
  change Fintype.card (C.Fiber (markerLabel n)) = _
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro o
  change C.label o = markerLabel n ↔ Nat.card o.orbit = 3
  rw [← Nat.card_congr (C.pointEquiv o)]
  exact (point_card_eq_three_iff n (C.label o)).symm

/-- The complete original marker profile, with the fixed and S3 counts
identified intrinsically from H. Every exterior projection remains full. -/
theorem exists_complete_profile (n : ℕ) (hdegree : Fintype.card X ≤ n) (hfits : Fits H) :
    ∃ p : ℕ, ∃ m : BinaryExteriorOrbitMenu.Label n → ℕ,
    ∃ e : RepeatedMarkerCompleteProfile.ModelPoints (BinaryExteriorOrbitMenu.points n)
        m p (orbitCount H 3) (orbitCount H 1) ≃ X,
      OrbitProfileFullOn (action n) e H := by
  choose label pointEquiv himage using orbit_cover H n hdegree hfits
  let C : OrbitProfileFromOrbits.Data H (action n) := ⟨label,pointEquiv,himage⟩
  let p := C.multiplicity (pairLabel n)
  let m : BinaryExteriorOrbitMenu.Label n → ℕ := fun i => C.multiplicity (exteriorLabel i)
  have hm : RepeatedMarkerCompleteProfile.multiplicity m p (orbitCount H 3) (orbitCount H 1) =
      C.multiplicity := by
    funext i
    rcases i with a | (a | (a | i))
    · cases a
      exact (multiplicity_fixed H n C).symm
    · cases a
      exact (multiplicity_marker H n C).symm
    · cases a
      rfl
    · rfl
  refine ⟨p,m,?_⟩
  change ∃ e : OrbitProfilePoints (points n)
      (RepeatedMarkerCompleteProfile.multiplicity m p (orbitCount H 3) (orbitCount H 1)) ≃ X,
    OrbitProfileFullOn (action n) e H
  rw [hm]
  exact ⟨C.chart,C.chart_full⟩

end SymmetricSubgroupAsymptotics.RepeatedMarkerOrbitProfiles

end
