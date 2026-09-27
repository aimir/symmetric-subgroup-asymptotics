import SymmetricSubgroupAsymptotics.OrbitProfileFromOrbits
import SymmetricSubgroupAsymptotics.BinaryTransitiveActionClasses

/-!
# A complete finite menu of original binary orbit actions

The menu consists of actual permutation-conjugacy classes in every positive
degree up to the given bound. Singleton and pair actions are included. It
contains one label per action type, and every original binary subgroup has
a simultaneous full profile in this menu. No catalogue or counting premise
is supplied, and no independence of the original orbit projections is used.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryBoundedOrbitMenu

abbrev Degree (n : ℕ) := {d : Fin (n+1) // 0 < d.1}

abbrev Label (n : ℕ) := Σ d : Degree n, BinaryTransitiveActionClass (Fin d.1.1)

def points (n : ℕ) (i : Label n) : Type := Fin i.1.1.1

instance pointsFintype (n : ℕ) (i : Label n) : Fintype (points n i) :=
  inferInstanceAs (Fintype (Fin i.1.1.1))

instance pointsNonempty (n : ℕ) (i : Label n) : Nonempty (points n i) :=
  ⟨⟨0,i.1.2⟩⟩

def action (n : ℕ) (i : Label n) : Subgroup (Equiv.Perm (points n i)) :=
  i.2.representative

theorem action_isPGroup (n : ℕ) (i : Label n) : IsPGroup 2 (action n i) :=
  i.2.representative_isPGroup

instance action_pretransitive (n : ℕ) (i : Label n) :
    MulAction.IsPretransitive (action n i) (points n i) :=
  i.2.representative_pretransitive

theorem action_transitive (n : ℕ) (i : Label n) (x y : points n i) :
    ∃ u : action n i, (u : Equiv.Perm (points n i)) x = y :=
  MulAction.exists_smul_eq (action n i) x y

@[simp] theorem point_card (n : ℕ) (i : Label n) :
    Fintype.card (points n i) = i.1.1.1 := Fintype.card_fin _

theorem point_card_pos (n : ℕ) (i : Label n) : 0 < Fintype.card (points n i) :=
  Fintype.card_pos

theorem point_card_le (n : ℕ) (i : Label n) : Fintype.card (points n i) ≤ n := by
  rw [point_card]
  exact Nat.le_of_lt_succ i.1.1.2

private theorem relabel_eq_conj {X : Type*} (c : Equiv.Perm X)
    (V : Subgroup (Equiv.Perm X)) :
    relabelSubgroup c V = MulAut.conj c • V := by
  change V.map c.permCongrHom.toMonoidHom = _
  rw [Subgroup.pointwise_smul_def]
  congr 1

/-- Different widths and different actual same-width conjugacy classes
are separated. In particular conjugate actions do not acquire new labels. -/
theorem action_separated (n : ℕ) : OrbitActionTypesSeparated (points n) (action n) := by
  rintro ⟨d,i⟩ ⟨d',i'⟩ e hforward hbackward
  have hd : d = d' := by
    apply Subtype.ext
    apply Fin.ext
    have hc : Nat.card (Fin d.1.1) = Nat.card (Fin d'.1.1) := Nat.card_congr e
    simpa only [Nat.card_fin] using hc
  subst d'
  have he : relabelSubgroup e i.representative = i'.representative := by
    ext v
    rw [mem_relabelSubgroup]
    constructor
    · intro hv
      have h := hforward _ hv
      change e.permCongr (e.permCongr.symm v) ∈ i'.representative at h
      rwa [Equiv.apply_symm_apply] at h
    · exact hbackward v
  have hi : i = i' := BinaryTransitiveActionClass.representative_separated i i' e
    ((relabel_eq_conj e i.representative).symm.trans he)
  subst i'
  rfl

section OriginalOrbits

variable {X : Type} [Fintype X] (H : Subgroup (Equiv.Perm X))

/-- Orbit-local coverage only needs a bound on the displayed orbit, not on
the ambient permutation set.  This is essential when an odd marker has
already consumed points outside the binary orbit. -/
theorem orbit_cover_of_orbit_card_le (n : ℕ)
    (o : OrbitProfileFromOrbits.Orbit H)
    (hbinary : IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H o))
    (hbound : Nat.card o.orbit ≤ n) :
    ∃ i : Label n, ∃ e : points n i ≃ o.orbit,
      relabelSubgroup e (action n i) = OrbitProfileFromOrbits.orbitImage H o := by
  letI : Fintype o.orbit := Fintype.ofFinite _
  letI : Nonempty o.orbit := by
    obtain ⟨x,hx⟩ := MulAction.orbitRel.Quotient.nonempty_orbit o
    exact ⟨⟨x,hx⟩⟩
  have hbound' : Fintype.card o.orbit ≤ n := by
    rwa [← Nat.card_eq_fintype_card]
  let d : Degree n := ⟨⟨Fintype.card o.orbit,Nat.lt_succ_of_le hbound'⟩,Fintype.card_pos⟩
  let e : Fin d.1.1 ≃ o.orbit := (Fintype.equivFin o.orbit).symm
  let V : Subgroup (Equiv.Perm (Fin d.1.1)) :=
    relabelSubgroup e.symm (OrbitProfileFromOrbits.orbitImage H o)
  have hV : IsPGroup 2 V := hbinary.map e.symm.permCongrHom.toMonoidHom
  have htrans : MulAction.IsPretransitive V (Fin d.1.1) := by
    constructor
    intro x y
    obtain ⟨h,hh⟩ := MulAction.exists_smul_eq H (e x) (e y)
    let v : V := ⟨e.symm.permCongr (MulAction.toPermHom H o.orbit h),by
      change _ ∈ (OrbitProfileFromOrbits.orbitImage H o).map e.symm.permCongrHom.toMonoidHom
      exact ⟨MulAction.toPermHom H o.orbit h,⟨h,rfl⟩,rfl⟩⟩
    refine ⟨v,?_⟩
    change e.symm (h • e x) = y
    rw [hh,Equiv.symm_apply_apply]
  obtain ⟨i,c,hc⟩ := BinaryTransitiveActionClass.representative_cover V hV htrans
  have hc' : relabelSubgroup c V = i.representative :=
    (relabel_eq_conj c V).trans hc
  refine ⟨⟨d,i⟩,c.symm.trans e,?_⟩
  change relabelSubgroup (c.symm.trans e) i.representative = _
  calc
    _ = relabelSubgroup e (relabelSubgroup c.symm i.representative) :=
      (relabelSubgroup_trans c.symm e i.representative).symm
    _ = relabelSubgroup e V := by rw [← hc',relabelSubgroup_symm]
    _ = _ := relabelSubgroup_symm e.symm (OrbitProfileFromOrbits.orbitImage H o)

/-- The binaryity premise concerns this literal original orbit image;
the original H may have other nonbinary orbit images. -/
theorem orbit_cover (n : ℕ) (hdegree : Fintype.card X ≤ n)
    (o : OrbitProfileFromOrbits.Orbit H)
    (hbinary : IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H o)) :
    ∃ i : Label n, ∃ e : points n i ≃ o.orbit,
      relabelSubgroup e (action n i) = OrbitProfileFromOrbits.orbitImage H o := by
  apply orbit_cover_of_orbit_card_le H n o hbinary
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_le_of_injective (fun x : o.orbit => (x : X))
    Subtype.val_injective).trans hdegree

/-- All binary original orbit images are installed simultaneously in one
finite menu, with their full coordinate actions and correlations retained. -/
theorem exists_profile_of_orbit_images (n : ℕ) (hdegree : Fintype.card X ≤ n)
    (hbinary : ∀ o : OrbitProfileFromOrbits.Orbit H,
      IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H o)) :
    ∃ m : Label n → ℕ, ∃ e : OrbitProfilePoints (points n) m ≃ X,
      OrbitProfileFullOn (action n) e H :=
  OrbitProfileFromOrbits.exists_profile_of_orbit_charts H (action n)
    (fun o => orbit_cover H n hdegree o (hbinary o))

/-- Every actual binary subgroup on the original bounded point set is
covered. No original full-profile or cardinality bound is supplied. -/
theorem exists_profile (n : ℕ) (hdegree : Fintype.card X ≤ n) (hH : IsPGroup 2 H) :
    ∃ m : Label n → ℕ, ∃ e : OrbitProfilePoints (points n) m ≃ X,
      OrbitProfileFullOn (action n) e H := by
  apply exists_profile_of_orbit_images H n hdegree
  intro o
  exact hH.of_surjective (MulAction.toPermHom H o.orbit).rangeRestrict
    (MulAction.toPermHom H o.orbit).rangeRestrict_surjective

end OriginalOrbits

end SymmetricSubgroupAsymptotics.BinaryBoundedOrbitMenu

end
