import SymmetricSubgroupAsymptotics.OrbitProfileSingletonExtraction
import SymmetricSubgroupAsymptotics.RepeatedMarkerFixedProfileBound

/-!
# Original marker profiles including all fixed points

Singletons, S3 markers, the single critical pair color, and the remaining
original actions have distinct color positions. Singleton extraction and
the actual marker presentation cover are composed before normalization.
The original f! divisor and every exterior action are retained.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerCompleteProfile

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (m : α → ℕ) (U : ∀ a, Subgroup (Equiv.Perm (Ω a)))

abbrev MovingPoints := RepeatedOddMarkerPhysicalProfile.points (RepeatedMarkerMergedProfile.points Ω)
abbrev MovingMultiplicity (p g : ℕ) := RepeatedOddMarkerPhysicalProfile.multiplicity
  (RepeatedMarkerMergedProfile.multiplicity m p) g
abbrev MovingAction := RepeatedOddMarkerPhysicalProfile.action
  (RepeatedMarkerMergedProfile.points Ω) (RepeatedMarkerMergedProfile.action Ω U)

abbrev points := OrbitProfileSingletonExtraction.points (MovingPoints Ω)
abbrev action := OrbitProfileSingletonExtraction.action (MovingPoints Ω) (MovingAction Ω U)
abbrev multiplicity (p g f : ℕ) :=
  OrbitProfileSingletonExtraction.multiplicity (MovingMultiplicity m p g) f
abbrev ModelPoints (p g f : ℕ) := OrbitProfilePoints (points Ω) (multiplicity m p g f)
abbrev Family (p g f : ℕ) (X : Type) :=
  FullOrbitProfileOn (points Ω) (multiplicity m p g f) (action Ω U) X

def sourceDegree (p g f : ℕ) : ℕ := f + (3*g + (2*p + RepeatedMarkerMergedProfile.exteriorDegree Ω m))

theorem moving_degree (p g : ℕ) :
    OrbitProfileSingletonExtraction.remainingDegree (MovingPoints Ω) (MovingMultiplicity m p g) =
      3*g + (2*p + RepeatedMarkerMergedProfile.exteriorDegree Ω m) := by
  change (∑ a, MovingMultiplicity m p g a * Fintype.card (MovingPoints Ω a)) = _
  rw [RepeatedOddMarkerPhysicalProfile.physicalDegree,RepeatedMarkerMergedProfile.degree]

theorem degree (p g f : ℕ) :
    (∑ a, multiplicity m p g f a * Fintype.card (points Ω a)) = sourceDegree Ω m p g f := by
  change (∑ a, OrbitProfileSingletonExtraction.multiplicity (MovingMultiplicity m p g) f a *
    Fintype.card (OrbitProfileSingletonExtraction.points (MovingPoints Ω) a)) = _
  rw [OrbitProfileSingletonExtraction.degree,moving_degree]
  rfl

theorem moving_transitive
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y) :
    ∀ a (x y : MovingPoints Ω a), ∃ u : MovingAction Ω U a,
      (u : Equiv.Perm (MovingPoints Ω a)) x = y :=
  RepeatedOddMarkerPhysicalProfile.action_transitive _ _
    (RepeatedMarkerMergedProfile.action_transitive Ω U htrans)

theorem moving_separated (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegreeTwo : ∀ a, Fintype.card (Ω a) ≠ 2) :
    OrbitActionTypesSeparated (MovingPoints Ω) (MovingAction Ω U) :=
  RepeatedOddMarkerPhysicalProfile.action_separated _ _
    (RepeatedMarkerMergedProfile.action_separated Ω U hsep hdegreeTwo)
    (RepeatedOddMarkerPhysicalBinary.exteriorDegree_ne_three _ _
      (RepeatedMarkerFixedProfileBound.action_isPGroup Ω U hU)
      (RepeatedMarkerMergedProfile.action_transitive Ω U htrans))

theorem moving_degree_ne_one (hdegreeOne : ∀ a, Fintype.card (Ω a) ≠ 1) :
    ∀ a, Fintype.card (MovingPoints Ω a) ≠ 1 := by
  intro a
  cases a with
  | inl a =>
    cases a
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (Fin 3) ≠ 1
    norm_num
  | inr a =>
    cases a with
    | inl a =>
      cases a
      change Fintype.card (RepeatedMarkerMergedProfile.points Ω (.inl PUnit.unit)) ≠ 1
      rw [RepeatedMarkerMergedProfile.point_card_pair]
      decide
    | inr a => exact hdegreeOne a

/-- The fixed-point factorial is extracted from the same actual whole
profile before the marker-image presentation cover is applied. -/
theorem card_restricted_le (p g f : ℕ) {X : Type}
    (chart : ModelPoints Ω m p g f ≃ X)
    (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegreeOne : ∀ a, Fintype.card (Ω a) ≠ 1)
    (hdegreeTwo : ∀ a, Fintype.card (Ω a) ≠ 2)
    (P : Subgroup (Equiv.Perm X) → Prop) :
    (Nat.card {H : Family Ω m U p g f X // P H.1} : ℚ) ≤
      ∑ q : RepeatedMarkerPresentationSum.Width (ι := Fin g),
        ((sourceDegree Ω m p g f).factorial : ℚ) /
          (2*(q.1+p) + RepeatedMarkerMergedProfile.exteriorDegree Ω m).factorial *
        ((2 : ℚ)^q.1 * RepeatedMarkerAllocationWeights.markerProfileSum (Q := Fin q.1) g /
          ((6 : ℚ)^g * f.factorial)) * (((q.1+p).factorial : ℚ) / p.factorial) *
          Nat.card (RepeatedMarkerFixedProfileBound.CollapsedFamily Ω m U p q.1) := by
  have hs := OrbitProfileSingletonExtraction.card_restricted_physical_le
    (MovingPoints Ω) (MovingMultiplicity m p g) (MovingAction Ω U) f chart (Equiv.refl _)
    (moving_transitive Ω U htrans) (moving_separated Ω U hU htrans hsep hdegreeTwo)
    (moving_degree_ne_one Ω hdegreeOne) P
  rw [moving_degree Ω m p g] at hs
  have hm := RepeatedMarkerFixedProfileBound.card_physical_le Ω m U p g (Equiv.refl _)
    hU htrans hsep hdegreeTwo
  apply hs.trans
  apply (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hfact (n : ℕ) : (n.factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h6 : (6 : ℚ)^g ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold sourceDegree
  field_simp [hfact,h6] <;> ring

/-- Every complete source color is an actual transitive action. -/
theorem action_transitive
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y) :
    ∀ a (x y : points Ω a), ∃ u : action Ω U a,
      (u : Equiv.Perm (points Ω a)) x = y :=
  OrbitProfileSingletonExtraction.action_transitive _ _ (moving_transitive Ω U htrans)

theorem action_separated (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegreeOne : ∀ a, Fintype.card (Ω a) ≠ 1)
    (hdegreeTwo : ∀ a, Fintype.card (Ω a) ≠ 2) :
    OrbitActionTypesSeparated (points Ω) (action Ω U) :=
  OrbitProfileSingletonExtraction.action_separated _ _
    (moving_separated Ω U hU htrans hsep hdegreeTwo) (moving_degree_ne_one Ω hdegreeOne)

end SymmetricSubgroupAsymptotics.RepeatedMarkerCompleteProfile

end
