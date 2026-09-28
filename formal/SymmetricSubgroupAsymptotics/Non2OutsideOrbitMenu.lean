import SymmetricSubgroupAsymptotics.Non2OutsideOrbitPhysical

/-!
# Finite physical menu for the complete outside-orbit frontier

The menu has one label for every exact degree at least three and every
permutation-conjugacy class of non-2 transitive actions in that degree.  A
single selected bad orbit covers each original outside subgroup, while the
family attached to its label retains the whole subgroup and complement.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace RepeatedMarkerOwnerBound

abbrev OutsideFitsFamilyAt (n : ℕ) :=
  {H : OrdinaryRemainderSubgroups n //
    ¬ RepeatedMarkerOrbitProfiles.Fits H.1}

theorem outsideFitsAt_hasOrbit {n : ℕ}
    (H : OutsideFitsFamilyAt n) : Nonempty (OutsideOrbit H.1.1) := by
  have hbad := H.2
  change ¬ ∀ o : OrbitProfileFromOrbits.Orbit H.1.1,
    IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H.1.1 o) ∨
      ∃ e : Fin 3 ≃ o.orbit,
        relabelSubgroup e oddMarkerActionSubgroup =
          OrbitProfileFromOrbits.orbitImage H.1.1 o at hbad
  push Not at hbad
  obtain ⟨o, hp, hs⟩ := hbad
  exact ⟨⟨o, hp, not_exists.mpr hs⟩⟩

abbrev Non2OutsideDegree (n : ℕ) :=
  {d : Fin (n+1) // 3 ≤ d.1}

abbrev Non2OutsideActionLabel (n : ℕ) :=
  Σ d : Non2OutsideDegree n,
    Non2TransitiveActionClass (Fin d.1.1)

def non2OutsideWidth {n : ℕ} (i : Non2OutsideActionLabel n) : ℕ :=
  i.1.1.1

def non2OutsideAction {n : ℕ} (i : Non2OutsideActionLabel n) :
    Subgroup (Equiv.Perm (Fin (non2OutsideWidth i))) :=
  i.2.representative

theorem non2OutsideWidth_three_le {n : ℕ}
    (i : Non2OutsideActionLabel n) : 3 ≤ non2OutsideWidth i :=
  i.1.2

theorem non2OutsideWidth_le {n : ℕ}
    (i : Non2OutsideActionLabel n) : non2OutsideWidth i ≤ n := by
  unfold non2OutsideWidth
  exact Nat.le_of_lt_succ i.1.1.2

def non2OutsidePredicate {n : ℕ} (i : Non2OutsideActionLabel n) :=
  fusionWidthOrdinaryRemainderPredicate (non2OutsideAction i)
    (non2OutsideWidth_le i)

theorem non2OutsidePredicate_natural {n : ℕ}
    (i : Non2OutsideActionLabel n) :
    FusionOrbitNatural (non2OutsideAction i) (non2OutsidePredicate i) :=
  fusionWidthOrdinaryRemainderPredicate_natural
    (non2OutsideAction i) (non2OutsideWidth_le i)

/-- The outside remainder as a literal set of original permutation
subgroups, rather than as an iterated subtype. -/
def OutsideFitsSubgroupSetAt (n : ℕ) :
    Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | ¬ IsCriticalSubgroup n H ∧
    ¬ RepeatedMarkerOrbitProfiles.Fits H}

abbrev OutsideFitsSubgroupSet (N epsilon : ℕ) :=
  OutsideFitsSubgroupSetAt (2*N+epsilon)

def outsideFitsSubgroupSetAtEquiv (n : ℕ) :
    OutsideFitsFamilyAt n ≃ OutsideFitsSubgroupSetAt n where
  toFun H := ⟨H.1.1, H.1.2, H.2⟩
  invFun H := ⟨⟨H.1, H.2.1⟩, H.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def outsideFitsSubgroupSetEquiv (N epsilon : ℕ) :
    OutsideFitsFamily N epsilon ≃ OutsideFitsSubgroupSet N epsilon where
  toFun H := ⟨H.1.1, H.1.2, H.2⟩
  invFun H := ⟨⟨H.1, H.2.1⟩, H.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem outsideFitsSubgroupSet_card (N epsilon : ℕ) :
    Nat.card (OutsideFitsSubgroupSet N epsilon) =
      Nat.card (OutsideFitsFamily N epsilon) := by
  rw [Nat.card_congr (outsideFitsSubgroupSetEquiv N epsilon).symm]

/-- The one selected bad orbit in arbitrary ambient degree.  Keeping this
choice named prevents a subgroup with several bad orbits from entering more
than one width sector. -/
def selectedOutsideOrbitAt {n : ℕ}
    (H : OutsideFitsFamilyAt n) : OutsideOrbit H.1.1 :=
  Classical.choice (outsideFitsAt_hasOrbit H)

def selectedOutsideWidthAt {n : ℕ}
    (H : OutsideFitsFamilyAt n) : ℕ :=
  Nat.card (selectedOutsideOrbitAt H).1.orbit

abbrev selectedOutsideOrbit (N epsilon : ℕ)
    (H : OutsideFitsFamily N epsilon) : OutsideOrbit H.1.1 :=
  selectedOutsideOrbitAt H

def selectedOutsideWidth (N epsilon : ℕ)
    (H : OutsideFitsFamily N epsilon) : ℕ :=
  selectedOutsideWidthAt H

theorem selectedOutsideWidthAt_gt_two {n : ℕ}
    (H : OutsideFitsFamilyAt n) :
    2 < selectedOutsideWidthAt H :=
  outsideOrbit_card_gt_two H.1.1 (selectedOutsideOrbitAt H)

theorem selectedOutsideWidth_gt_two (N epsilon : ℕ)
    (H : OutsideFitsFamily N epsilon) :
    2 < selectedOutsideWidth N epsilon H :=
  selectedOutsideWidthAt_gt_two H

/-- The selected orbit gives a representative of its exact width, and the
whole original subgroup enters that representative's canonical family. -/
theorem outsideFitsAt_selected_physical_cover {n : ℕ}
    (H : OutsideFitsFamilyAt n) :
    ∃ i : Non2OutsideActionLabel n,
      non2OutsideWidth i = selectedOutsideWidthAt H ∧
      H.1.1 ∈ FusionWidthCanonicalFamily (non2OutsideAction i)
        (non2OutsideWidth_le i) (non2OutsidePredicate i) := by
  let o : OutsideOrbit H.1.1 := selectedOutsideOrbitAt H
  have hle : Nat.card o.1.orbit ≤ n := by
    have hcard := Nat.card_le_card_of_injective
      (Subtype.val : o.1.orbit → Fin n) Subtype.val_injective
    simpa only [Nat.card_fin] using hcard
  let d : Non2OutsideDegree n :=
    ⟨⟨Nat.card o.1.orbit, Nat.lt_succ_of_le hle⟩,
      outsideOrbit_card_gt_two H.1.1 o⟩
  obtain ⟨i, eO, himage⟩ := Non2TransitiveActionClass.orbit_cover
    H.1.1 o.1 (w := d.1.1) (by rfl) o.2.1
  refine ⟨⟨d, i⟩, rfl, ?_⟩
  exact FusionOrbitProfileChart.mem_widthCanonicalFamily_ordinary
    H.1.1 H.1.2 o.1 (by rfl) (non2OutsideWidth_le ⟨d, i⟩)
      i.representative eO himage

/-- Every outside subgroup enters one member of the complete non-2 action
menu.  There is no orbit multiplicity in this cover: one bad orbit is chosen
only to produce the label, and the covered object is the original subgroup.
-/
theorem outsideFits_physical_cover (N epsilon : ℕ)
    (H : OutsideFitsFamily N epsilon) :
    ∃ i : Non2OutsideActionLabel (2*N+epsilon),
      H.1.1 ∈ FusionWidthCanonicalFamily (non2OutsideAction i)
        (non2OutsideWidth_le i) (non2OutsidePredicate i) := by
  obtain ⟨i, _, hi⟩ := outsideFitsAt_selected_physical_cover H
  exact ⟨i, hi⟩

theorem outsideFitsSubgroupSet_physical_cover (N epsilon : ℕ)
    (H : Subgroup (Equiv.Perm (Fin (2*N+epsilon))))
    (hH : H ∈ OutsideFitsSubgroupSet N epsilon) :
    ∃ i : Non2OutsideActionLabel (2*N+epsilon),
      H ∈ FusionWidthCanonicalFamily (non2OutsideAction i)
        (non2OutsideWidth_le i) (non2OutsidePredicate i) := by
  let H' : OutsideFitsFamily N epsilon := ⟨⟨H,hH.1⟩,hH.2⟩
  simpa only [H'] using outsideFits_physical_cover N epsilon H'

end RepeatedMarkerOwnerBound
end SymmetricSubgroupAsymptotics

end
