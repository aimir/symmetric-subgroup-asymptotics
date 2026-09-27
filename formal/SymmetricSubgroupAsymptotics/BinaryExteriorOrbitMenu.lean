import SymmetricSubgroupAsymptotics.BinaryBoundedOrbitMenu
import SymmetricSubgroupAsymptotics.RepeatedMarkerPositiveRecurrence

/-!
# The complete binary exterior menu after singleton and pair removal

The label restriction uses actual point degrees. Every original binary
orbit of size other than one or two enters this restricted menu. Its binary,
transitive, separated action properties install the already proved positive
marker recurrence with no supplied menu-property or counting premise.

That recurrence counts the actual full-profile family with the explicit
singleton, C2 and S3 colors. Identifying an arbitrary owner family with this
profile family still requires its original per-orbit binary-or-S3 coverage;
arbitrary odd orbit actions are not included.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryExteriorOrbitMenu

abbrev Label (n : ℕ) :=
  {i : BinaryBoundedOrbitMenu.Label n //
    2 < Fintype.card (BinaryBoundedOrbitMenu.points n i)}

abbrev points (n : ℕ) (i : Label n) := BinaryBoundedOrbitMenu.points n i.1

abbrev action (n : ℕ) (i : Label n) : Subgroup (Equiv.Perm (points n i)) :=
  BinaryBoundedOrbitMenu.action n i.1

theorem action_isPGroup (n : ℕ) (i : Label n) : IsPGroup 2 (action n i) :=
  BinaryBoundedOrbitMenu.action_isPGroup n i.1

theorem action_transitive (n : ℕ) (i : Label n) (x y : points n i) :
    ∃ u : action n i, (u : Equiv.Perm (points n i)) x = y :=
  BinaryBoundedOrbitMenu.action_transitive n i.1 x y

theorem action_separated (n : ℕ) : OrbitActionTypesSeparated (points n) (action n) := by
  intro i j e hforward hbackward
  exact Subtype.ext (BinaryBoundedOrbitMenu.action_separated n i.1 j.1 e hforward hbackward)

theorem point_card_ne_one (n : ℕ) (i : Label n) : Fintype.card (points n i) ≠ 1 := by
  have h : 2 < Fintype.card (points n i) := i.2
  exact Nat.ne_of_gt (lt_trans (by decide : 1 < 2) h)

theorem point_card_ne_two (n : ℕ) (i : Label n) : Fintype.card (points n i) ≠ 2 := by
  exact Nat.ne_of_gt i.2

section OriginalOrbits

variable {X : Type} [Fintype X] (H : Subgroup (Equiv.Perm X))

/-- Excluding the two literal small orbit sizes is sufficient; no
preselected action catalogue or complete-profile hypothesis is supplied. -/
theorem orbit_cover_of_orbit_card_le (n : ℕ)
    (o : OrbitProfileFromOrbits.Orbit H)
    (hbinary : IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H o))
    (hneOne : Nat.card o.orbit ≠ 1) (hneTwo : Nat.card o.orbit ≠ 2)
    (hbound : Nat.card o.orbit ≤ n) :
    ∃ i : Label n, ∃ e : points n i ≃ o.orbit,
      relabelSubgroup e (action n i) = OrbitProfileFromOrbits.orbitImage H o := by
  obtain ⟨i,e,he⟩ := BinaryBoundedOrbitMenu.orbit_cover_of_orbit_card_le
    H n o hbinary hbound
  have hc : Fintype.card (BinaryBoundedOrbitMenu.points n i) = Nat.card o.orbit := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr e
  have hp := BinaryBoundedOrbitMenu.point_card_pos n i
  have hi : 2 < Fintype.card (BinaryBoundedOrbitMenu.points n i) := by omega
  exact ⟨⟨i,hi⟩,e,he⟩

theorem orbit_cover (n : ℕ) (hdegree : Fintype.card X ≤ n)
    (o : OrbitProfileFromOrbits.Orbit H)
    (hbinary : IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H o))
    (hneOne : Nat.card o.orbit ≠ 1) (hneTwo : Nat.card o.orbit ≠ 2) :
    ∃ i : Label n, ∃ e : points n i ≃ o.orbit,
      relabelSubgroup e (action n i) = OrbitProfileFromOrbits.orbitImage H o := by
  apply orbit_cover_of_orbit_card_le H n o hbinary hneOne hneTwo
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_le_of_injective (fun x : o.orbit => (x : X))
    Subtype.val_injective).trans hdegree

/-- All original exterior orbits are covered simultaneously. The actual
subgroup and all relations between its orbit actions are retained. -/
theorem exists_profile_of_orbit_images (n : ℕ) (hdegree : Fintype.card X ≤ n)
    (hbinary : ∀ o : OrbitProfileFromOrbits.Orbit H,
      IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H o))
    (hneOne : ∀ o : OrbitProfileFromOrbits.Orbit H, Nat.card o.orbit ≠ 1)
    (hneTwo : ∀ o : OrbitProfileFromOrbits.Orbit H, Nat.card o.orbit ≠ 2) :
    ∃ m : Label n → ℕ, ∃ e : OrbitProfilePoints (points n) m ≃ X,
      OrbitProfileFullOn (action n) e H :=
  OrbitProfileFromOrbits.exists_profile_of_orbit_charts H (action n)
    (fun o => orbit_cover H n hdegree o (hbinary o) (hneOne o) (hneTwo o))

theorem exists_profile (n : ℕ) (hdegree : Fintype.card X ≤ n) (hH : IsPGroup 2 H)
    (hneOne : ∀ o : OrbitProfileFromOrbits.Orbit H, Nat.card o.orbit ≠ 1)
    (hneTwo : ∀ o : OrbitProfileFromOrbits.Orbit H, Nat.card o.orbit ≠ 2) :
    ∃ m : Label n → ℕ, ∃ e : OrbitProfilePoints (points n) m ≃ X,
      OrbitProfileFullOn (action n) e H := by
  apply exists_profile_of_orbit_images H n hdegree _ hneOne hneTwo
  intro o
  exact hH.of_surjective (MulAction.toPermHom H o.orbit).rangeRestrict
    (MulAction.toPermHom H o.orbit).rangeRestrict_surjective

end OriginalOrbits

/-- The actual positive-defect full-profile family with the exhaustive
bounded binary exterior menu. All support and multiplicity witnesses are
forgotten before counting the original Fin(2N+epsilon) subgroup. -/
abbrev PositiveFamily (N epsilon : ℕ)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) :=
  RepeatedMarkerPositiveFamily.Family (points (2*N+epsilon)) (action (2*N+epsilon))
    N epsilon P

/-- The original positive-defect physical count enters the ordinary
forward row with every action-menu property proved internally. This is
an upper bound for arbitrary original exclusions P. -/
theorem positive_card_div_benchmark_le (N epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) :
    (Nat.card (PositiveFamily N epsilon P) : ℝ) / exactBenchmark (2*N+epsilon) ≤
      ∑ m ∈ Finset.range (2*N+epsilon),
        MarkerDegreeForwardRow.kernel (2*N+epsilon) m * ordinarySubgroupRatio m :=
  RepeatedMarkerPositiveRecurrence.card_div_benchmark_le_degree_row
    (points (2*N+epsilon)) (action (2*N+epsilon))
    (action_isPGroup (2*N+epsilon)) (action_transitive (2*N+epsilon))
    (action_separated (2*N+epsilon)) (point_card_ne_one (2*N+epsilon))
    (point_card_ne_two (2*N+epsilon)) N epsilon hepsilon P

end SymmetricSubgroupAsymptotics.BinaryExteriorOrbitMenu

end
