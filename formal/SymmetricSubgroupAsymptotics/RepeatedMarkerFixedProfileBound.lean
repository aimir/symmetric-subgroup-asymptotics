import SymmetricSubgroupAsymptotics.RepeatedMarkerMergedProfile
import SymmetricSubgroupAsymptotics.RepeatedMarkerPresentationSum
import SymmetricSubgroupAsymptotics.RepeatedOddMarkerPhysicalBinary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Actual fixed-profile upper bound with original marker and pair weights

The target is the complete natural merged profile. Every original marker
image is covered automatically; no collapsed-model cardinality premise
or prior bound on ordinary subgroup counts is used. Arbitrary exclusions
on the original physical subgroup may be dropped by inclusion. This
unrestricted target is intended for the positive-defect forward row;
the zero-defect remainder target requires its separate restriction.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerFixedProfileBound

open RepeatedMarkerMergedProfile RepeatedCharacterCollapse RepeatedCharacterPresentations

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (m : α → ℕ) (U : ∀ a, Subgroup (Equiv.Perm (Ω a)))

private theorem sign_isPGroup : IsPGroup 2 Sign := by
  intro x
  refine ⟨1, ?_⟩
  simpa only [pow_one] using binary_mul_pow_two x

theorem action_isPGroup (hU : ∀ a, IsPGroup 2 (U a)) :
    ∀ a, IsPGroup 2 (action Ω U a) := by
  intro a
  cases a with
  | inl _ => exact sign_isPGroup.of_equiv binaryMarkerLocalEquiv
  | inr a => exact hU a

private theorem nontrivial_sign_surjective {G : Type*} [Group G]
    (χ : G →* Sign) (hχ : χ ≠ 1) : Function.Surjective χ := by
  have hx : ∃ x, χ x ≠ 1 := by
    by_contra h
    apply hχ
    apply MonoidHom.ext
    intro x
    exact not_not.mp (fun hx => h ⟨x, hx⟩)
  obtain ⟨x, hx⟩ := hx
  intro z
  by_cases hz : z = 1
  · exact ⟨1, (map_one χ).trans hz.symm⟩
  · refine ⟨x, ?_⟩
    apply Multiplicative.toAdd.injective
    have htwo : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a = b := by decide
    apply htwo
    · intro h
      exact hx (Multiplicative.toAdd.injective h)
    · intro h
      exact hz (Multiplicative.toAdd.injective h)

abbrev ImagePredicate (p g : ℕ) :=
  RepeatedOddMarkerPhysicalProfile.imagePredicate (points Ω) (RepeatedMarkerMergedProfile.multiplicity m p)
    (action Ω U) g

abbrev CollapsedModel (p q : ℕ) :=
  OrbitProfileReindexedProduct.ModelFamily (RepeatedMarkerMergedProfile.multiplicity m (q+p)) (action Ω U)
    (retainedChart Ω m U q p) (fun _ => True)

abbrev CollapsedFamily (p q : ℕ) :=
  OrbitProfileReindexedProduct.PhysicalFamily (RepeatedMarkerMergedProfile.multiplicity m (q+p)) (action Ω U)
    (fun _ => True) (ModelPoints Ω m (q+p))

abbrev OriginalFamily (p g : ℕ) (X : Type) :=
  RepeatedOddMarkerPhysicalProfile.PhysicalFamily (points Ω) (RepeatedMarkerMergedProfile.multiplicity m p)
    (action Ω U) g X

def Allowed (p g : ℕ) (q : RepeatedMarkerPresentationSum.Width (ι := Fin g))
    (Y : Subgroup ((Fin q.1 → Sign) × Original Ω m U p)) : Prop :=
  OrbitProfileProductFull (RepeatedMarkerMergedProfile.multiplicity m (q.1+p)) (action Ω U)
    (Y.map (retainedChart Ω m U q.1 p).toMonoidHom) ∧ True

/-- Every chosen original presentation has full new pair coordinates and
all old original projections. The complete target needs no extra cover input. -/
theorem present_allowed (p g : ℕ)
    (B : RepeatedOddMarkerImageSum.ImageState (ImagePredicate Ω m U p g)) :
    Allowed Ω m U p g (present B.1).1 (present B.1).2.2 := by
  have ha := RepeatedOddMarkerPresentationBound.present_admissible
    (ImagePredicate Ω m U p g) B
  constructor
  · apply retainedChart_full Ω m U (present B.1).1.1 p (present B.1).2.2
    · intro i
      exact nontrivial_sign_surjective _ (ha.1 i)
    · have hOld := ha.2
      change OrbitProfileProductFull (RepeatedMarkerMergedProfile.multiplicity m p) (action Ω U)
        ((allocationExpanded (present B.1).2.1.1 (present B.1).2.2).map
          (MonoidHom.snd _ _)) at hOld
      rw [allocation_exterior] at hOld
      exact hOld
  · trivial

theorem modelWeight_le (p g : ℕ) (hU : ∀ a, IsPGroup 2 (U a)) :
    RepeatedOddMarkerPhysicalProfile.modelWeight (points Ω) (RepeatedMarkerMergedProfile.multiplicity m p)
      (action Ω U) g ≤
      ∑ q : RepeatedMarkerPresentationSum.Width (ι := Fin g),
        (g.factorial : ℚ) *
          RepeatedMarkerAllocationWeights.markerProfileSum (Q := Fin q.1) g *
          (Nat.card (CollapsedModel Ω m U p q.1) : ℚ) := by
  have h := RepeatedMarkerPresentationSum.familyWeight_le_factored
    (Allowed Ω m U p g)
    (orbitProfileProduct_isPGroup (RepeatedMarkerMergedProfile.multiplicity m p) (action Ω U) (action_isPGroup Ω U hU))
    (ImagePredicate Ω m U p g) (present_allowed Ω m U p g)
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro q _
  rw [RepeatedMarkerPresentationSum.allocationSum_fin_eq]
  rfl

theorem collapsed_card (p q : ℕ)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (Nat.card (CollapsedFamily Ω m U p q) : ℚ) =
      ((2*(q+p) + exteriorDegree Ω m).factorial : ℚ) *
        Nat.card (CollapsedModel Ω m U p q) /
        ((2 : ℚ)^(q+p) * (q+p).factorial * exteriorDenominator Ω m U) :=
  RepeatedMarkerMergedProfile.card_physical_rat Ω m U q p (fun _ => True) (Equiv.refl _)
    (by intro w hw K hK; trivial) htrans hsep hdegree

private theorem exteriorDenominator_pos : (0 : ℚ) < exteriorDenominator Ω m U := by
  apply Finset.prod_pos
  intro a _
  exact mul_pos (pow_pos (Nat.cast_pos.mpr Nat.card_pos) _)
    (Nat.cast_pos.mpr (Nat.factorial_pos _))

private theorem weight_identity (n d g p q : ℕ) (H C E : ℚ) (hE : E ≠ 0) :
    (n.factorial : ℚ) * ((g.factorial : ℚ) * H * C) /
        ((6 : ℚ)^g * g.factorial * ((2 : ℚ)^p * p.factorial * E)) =
      ((n.factorial : ℚ) / d.factorial) * ((2 : ℚ)^q * H / (6 : ℚ)^g) *
        (((q+p).factorial : ℚ) / p.factorial) *
        ((d.factorial : ℚ) * C / ((2 : ℚ)^(q+p) * (q+p).factorial * E)) := by
  have hfact (a : ℕ) : (a.factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
  have h2 (a : ℕ) : (2 : ℚ)^a ≠ 0 := pow_ne_zero _ (by norm_num)
  have h6 : (6 : ℚ)^g ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [pow_add]
  field_simp [hfact, h2, h6, hE] <;> ring

/-- Complete fixed-profile original-weight inequality. Its targets are
actual natural physical families; no collapsed subgroup count is supplied.
The ratio (q+p)!/p! keeps the full presentation cost. -/
theorem card_physical_le (p g : ℕ) {X : Type}
    (chart : RepeatedOddMarkerPhysicalProfile.ModelPoints (points Ω) (RepeatedMarkerMergedProfile.multiplicity m p) g ≃ X)
    (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (Nat.card (OriginalFamily Ω m U p g X) : ℚ) ≤
      ∑ q : RepeatedMarkerPresentationSum.Width (ι := Fin g),
        (((3*g + (2*p + exteriorDegree Ω m)).factorial : ℚ) /
          (2*(q.1+p) + exteriorDegree Ω m).factorial) *
        ((2 : ℚ)^q.1 * RepeatedMarkerAllocationWeights.markerProfileSum (Q := Fin q.1) g /
          (6 : ℚ)^g) * (((q.1+p).factorial : ℚ) / p.factorial) *
          (Nat.card (CollapsedFamily Ω m U p q.1) : ℚ) := by
  have hphysical := RepeatedOddMarkerPhysicalBinary.card_physical_rat
    (points Ω) (RepeatedMarkerMergedProfile.multiplicity m p) (action Ω U) g chart (action_isPGroup Ω U hU)
    (action_transitive Ω U htrans) (action_separated Ω U hsep hdegree)
  have hden : RepeatedOddMarkerPhysicalProfile.exteriorDenominator
      (points Ω) (RepeatedMarkerMergedProfile.multiplicity m p) (action Ω U) =
      (2 : ℚ)^p * p.factorial * exteriorDenominator Ω m U :=
    denominator Ω m U p
  rw [degree Ω m p, hden] at hphysical
  rw [hphysical]
  calc
    _ ≤ ((3*g + (2*p + exteriorDegree Ω m)).factorial : ℚ) *
        (∑ q : RepeatedMarkerPresentationSum.Width (ι := Fin g),
          (g.factorial : ℚ) *
            RepeatedMarkerAllocationWeights.markerProfileSum (Q := Fin q.1) g *
            (Nat.card (CollapsedModel Ω m U p q.1) : ℚ)) /
        ((6 : ℚ)^g * g.factorial * ((2 : ℚ)^p * p.factorial * exteriorDenominator Ω m U)) := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left (modelWeight_le Ω m U p g hU) (Nat.cast_nonneg _)
      · exact mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _))
          (mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _))
            (exteriorDenominator_pos Ω m U).le)
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro q _
      rw [collapsed_card Ω m U p q.1 htrans hsep hdegree]
      exact weight_identity _ _ g p q.1 _ _ _ (ne_of_gt (exteriorDenominator_pos Ω m U))

/-- Arbitrary earlier ownership exclusions on the original physical group
are retained on the left and removed only by inclusion. -/
theorem card_restricted_physical_le (p g : ℕ) {X : Type}
    (chart : RepeatedOddMarkerPhysicalProfile.ModelPoints (points Ω) (RepeatedMarkerMergedProfile.multiplicity m p) g ≃ X)
    (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2)
    (P : Subgroup (Equiv.Perm X) → Prop) :
    (Nat.card {H : OriginalFamily Ω m U p g X // P H.1} : ℚ) ≤
      ∑ q : RepeatedMarkerPresentationSum.Width (ι := Fin g),
        (((3*g + (2*p + exteriorDegree Ω m)).factorial : ℚ) /
          (2*(q.1+p) + exteriorDegree Ω m).factorial) *
        ((2 : ℚ)^q.1 * RepeatedMarkerAllocationWeights.markerProfileSum (Q := Fin q.1) g /
          (6 : ℚ)^g) * (((q.1+p).factorial : ℚ) / p.factorial) *
          (Nat.card (CollapsedFamily Ω m U p q.1) : ℚ) := by
  letI : Finite X := Finite.of_equiv
    (RepeatedOddMarkerPhysicalProfile.ModelPoints (points Ω) (RepeatedMarkerMergedProfile.multiplicity m p) g) chart
  letI : Finite (OriginalFamily Ω m U p g X) :=
    Finite.of_injective (fun H : OriginalFamily Ω m U p g X => (H.1 : Set (Equiv.Perm X)))
      (fun _ _ h => Subtype.ext (SetLike.coe_injective h))
  apply le_trans ?_ (card_physical_le Ω m U p g chart hU htrans hsep hdegree)
  exact_mod_cast Nat.card_le_card_of_injective
    (fun H : {H : OriginalFamily Ω m U p g X // P H.1} => H.1) Subtype.val_injective

end SymmetricSubgroupAsymptotics.RepeatedMarkerFixedProfileBound

end
