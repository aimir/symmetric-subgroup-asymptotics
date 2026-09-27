import SymmetricSubgroupAsymptotics.BinaryExteriorOrbitMenu
import SymmetricSubgroupAsymptotics.BinaryPairE8Profile

/-!
# The binary exterior menu with the original E8 colour removed

The reversible four-pair construction must add an occurrence of the existing
E8 action type.  This residual menu removes precisely that conjugacy class
from the bounded binary exterior menu.  Adding the literal original E8 action
back as a head colour is separated, transitive, and exhaustive away from
singleton, pair, and E8 orbits.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryResidualOrbitMenu

def IsE8 (n : ℕ) (i : BinaryExteriorOrbitMenu.Label n) : Prop :=
  ∃ e : criticalActionPoints .e8 ≃ BinaryExteriorOrbitMenu.points n i,
    relabelSubgroup e (criticalActionSubgroup .e8) =
      BinaryExteriorOrbitMenu.action n i

abbrev Label (n : ℕ) :=
  {i : BinaryExteriorOrbitMenu.Label n // ¬ IsE8 n i}

abbrev points (n : ℕ) (i : Label n) := BinaryExteriorOrbitMenu.points n i.1
abbrev action (n : ℕ) (i : Label n) := BinaryExteriorOrbitMenu.action n i.1

theorem action_isPGroup (n : ℕ) (i : Label n) : IsPGroup 2 (action n i) :=
  BinaryExteriorOrbitMenu.action_isPGroup n i.1

theorem action_transitive (n : ℕ) (i : Label n) (x y : points n i) :
    ∃ u : action n i, (u : Equiv.Perm (points n i)) x = y :=
  BinaryExteriorOrbitMenu.action_transitive n i.1 x y

theorem point_card_ne_two (n : ℕ) (i : Label n) :
    Fintype.card (points n i) ≠ 2 :=
  BinaryExteriorOrbitMenu.point_card_ne_two n i.1

theorem action_separated (n : ℕ) : OrbitActionTypesSeparated (points n) (action n) := by
  intro i j e hf hb
  exact Subtype.ext (BinaryExteriorOrbitMenu.action_separated n i.1 j.1 e hf hb)

private theorem relabel_eq_of_biinclusion {X Y : Type*} (e : X ≃ Y)
    (A : Subgroup (Equiv.Perm X)) (B : Subgroup (Equiv.Perm Y))
    (hf : ∀ a ∈ A, e.permCongr a ∈ B)
    (hb : ∀ b ∈ B, e.symm.permCongr b ∈ A) :
    relabelSubgroup e A = B := by
  ext b
  rw [mem_relabelSubgroup]
  constructor
  · intro hb'
    have := hf _ hb'
    have he : e.permCongr (e.symm.permCongr b) = b := by
      apply Equiv.ext
      intro y
      simp
    rwa [he] at this
  · exact hb b

/-- The literal E8 head and every residual binary exterior action are
pairwise distinct original permutation-action types. -/
theorem e8_residual_separated (n : ℕ) :
    OrbitActionTypesSeparated
      (BinaryPairE8Profile.exteriorPoints (points n))
      (BinaryPairE8Profile.exteriorAction (points n) (action n)) := by
  intro i j e hf hb
  cases i with
  | inl i =>
    cases j with
    | inl j => cases i; cases j; rfl
    | inr j =>
      exfalso
      apply j.property
      exact ⟨e,relabel_eq_of_biinclusion e
        (criticalActionSubgroup .e8) (action n j) hf hb⟩
  | inr i =>
    cases j with
    | inl j =>
      exfalso
      apply i.property
      exact ⟨e.symm,relabel_eq_of_biinclusion e.symm
        (criticalActionSubgroup .e8) (action n i) hb hf⟩
    | inr j =>
      exact congrArg Sum.inr (action_separated n i j e hf hb)

section OriginalOrbits

variable {X : Type} [Fintype X] (H : Subgroup (Equiv.Perm X))

/-- Every binary orbit outside sizes one and two and outside the original
E8 conjugacy class has a label in the residual menu. -/
theorem orbit_cover_of_orbit_card_le (n : ℕ)
    (o : OrbitProfileFromOrbits.Orbit H)
    (hbinary : IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H o))
    (hneOne : Nat.card o.orbit ≠ 1) (hneTwo : Nat.card o.orbit ≠ 2)
    (hneE8 : ¬ ∃ e : criticalActionPoints .e8 ≃ o.orbit,
      relabelSubgroup e (criticalActionSubgroup .e8) =
        OrbitProfileFromOrbits.orbitImage H o)
    (hbound : Nat.card o.orbit ≤ n) :
    ∃ i : Label n, ∃ e : points n i ≃ o.orbit,
      relabelSubgroup e (action n i) = OrbitProfileFromOrbits.orbitImage H o := by
  obtain ⟨i,e,he⟩ := BinaryExteriorOrbitMenu.orbit_cover_of_orbit_card_le H n o
    hbinary hneOne hneTwo hbound
  have hi : ¬ IsE8 n i := by
    rintro ⟨c,hc⟩
    apply hneE8
    refine ⟨c.trans e,?_⟩
    calc
      relabelSubgroup (c.trans e) (criticalActionSubgroup .e8) =
          relabelSubgroup e (relabelSubgroup c (criticalActionSubgroup .e8)) :=
        (relabelSubgroup_trans c e _).symm
      _ = relabelSubgroup e (BinaryExteriorOrbitMenu.action n i) := by rw [hc]
      _ = _ := he
  exact ⟨⟨i,hi⟩,e,he⟩

theorem orbit_cover (n : ℕ) (hdegree : Fintype.card X ≤ n)
    (o : OrbitProfileFromOrbits.Orbit H)
    (hbinary : IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H o))
    (hneOne : Nat.card o.orbit ≠ 1) (hneTwo : Nat.card o.orbit ≠ 2)
    (hneE8 : ¬ ∃ e : criticalActionPoints .e8 ≃ o.orbit,
      relabelSubgroup e (criticalActionSubgroup .e8) =
        OrbitProfileFromOrbits.orbitImage H o) :
    ∃ i : Label n, ∃ e : points n i ≃ o.orbit,
      relabelSubgroup e (action n i) = OrbitProfileFromOrbits.orbitImage H o := by
  apply orbit_cover_of_orbit_card_le H n o hbinary hneOne hneTwo hneE8
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_le_of_injective (fun x : o.orbit => (x : X))
    Subtype.val_injective).trans hdegree

end OriginalOrbits

end SymmetricSubgroupAsymptotics.BinaryResidualOrbitMenu
