import SymmetricSubgroupAsymptotics.OddProfileActions

/-! Exact disjoint assembly of the two original odd critical orbit profiles. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The positive-rank guard excludes an S3 marker at total degree one. -/
abbrev OddCriticalProfileIndex (R : ℕ) :=
  (criticalProfiles R) ⊕ {_p : (criticalProfiles (R - 1)) // 0 < R}

def oddCriticalIndexPair (R : ℕ) : OddCriticalProfileIndex R → Bool × CriticalProfile
  | .inl p => (false, p.1)
  | .inr p => (true, p.1.1)

def oddCriticalIndexMultiplicity (R : ℕ) (p : OddCriticalProfileIndex R) :=
  oddCriticalMultiplicity (oddCriticalIndexPair R p).1 (oddCriticalIndexPair R p).2

theorem oddCriticalIndexPair_injective (R : ℕ) : Function.Injective (oddCriticalIndexPair R) := by
  intro p q h
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      apply congrArg Sum.inl
      exact Subtype.ext (congrArg Prod.snd h)
    | inr q => exact Bool.noConfusion (congrArg Prod.fst h)
  | inr p =>
    cases q with
    | inl q => exact Bool.noConfusion (congrArg Prod.fst h)
    | inr q =>
      apply congrArg Sum.inr
      apply Subtype.ext
      exact Subtype.ext (congrArg Prod.snd h)

theorem oddCriticalIndexMultiplicity_injective (R : ℕ) :
    Function.Injective (oddCriticalIndexMultiplicity R) :=
  oddCriticalMultiplicity_injective.comp (oddCriticalIndexPair_injective R)

theorem oddCriticalIndex_degree (R : ℕ) (p : OddCriticalProfileIndex R) :
    ∑ i, oddCriticalIndexMultiplicity R p i * Fintype.card (oddCriticalActionPoints i) =
      2 * R + 1 := by
  unfold oddCriticalIndexMultiplicity
  rw [oddCriticalMultiplicity_degree]
  cases p with
  | inl p =>
    have hp := (mem_criticalProfiles R p.1).mp p.2
    simp only [oddCriticalIndexPair, Bool.false_eq_true, ↓reduceIte, hp]
  | inr p =>
    have hp := (mem_criticalProfiles (R - 1) p.1.1).mp p.1.2
    have hR := p.2
    simp only [oddCriticalIndexPair, ↓reduceIte, hp]
    omega

/-- Actual subgroups of S_(2R+1) having exactly one permitted odd marker
and otherwise one of the four original binary critical actions. -/
abbrev OddCriticalSubgroups (R : ℕ) :=
  AssembledOrbitProfilesOn (oddCriticalIndexMultiplicity R)
    (fun p ↦ OrbitProfileFull (m := oddCriticalIndexMultiplicity R p) oddCriticalActionSubgroup 1)
    (Fin (2 * R + 1))

theorem oddCriticalSubgroups_card_indexed (R : ℕ) :
    (Nat.card (OddCriticalSubgroups R) : ℚ) =
      ((2 * R + 1).factorial : ℚ) * ∑ p : OddCriticalProfileIndex R,
        ((oddCriticalIndexPair R p).2.weight / (if (oddCriticalIndexPair R p).1 then 6 else 1)) *
          Nat.card (OddCriticalModelSubgroups (oddCriticalIndexPair R p).1 (oddCriticalIndexPair R p).2) := by
  have h := assembledOrbitProfilesOn_fin_card_rat
    (m := oddCriticalIndexMultiplicity R)
    (P := fun p ↦ OrbitProfileFull (m := oddCriticalIndexMultiplicity R p) oddCriticalActionSubgroup 1)
    (2 * R + 1) (oddCriticalIndex_degree R) (oddCriticalIndexMultiplicity_injective R)
    (fun _ _ h ↦ h)
    (fun p ↦ orbitProfileFull_family_natural (oddCriticalIndexMultiplicity R p) oddCriticalActionSubgroup)
    oddCriticalAction_transitive oddCriticalAction_types_separated
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  change _ = _
  rw [div_eq_mul_inv]
  change _ * _ * (∏ i, (Nat.card (Subgroup.normalizer (oddCriticalActionSubgroup i :
    Set (Equiv.Perm (oddCriticalActionPoints i)))) : ℚ) ^
    oddCriticalMultiplicity (oddCriticalIndexPair R p).1 (oddCriticalIndexPair R p).2 i *
      (oddCriticalMultiplicity (oddCriticalIndexPair R p).1 (oddCriticalIndexPair R p).2 i).factorial)⁻¹ = _
  rw [oddCriticalMultiplicity_weight]
  change ((2 * R + 1).factorial : ℚ) *
    (Nat.card (OddCriticalModelSubgroups (oddCriticalIndexPair R p).1
      (oddCriticalIndexPair R p).2) : ℚ) *
    ((oddCriticalIndexPair R p).2.weight / (if (oddCriticalIndexPair R p).1 then 6 else 1)) = _
  ring

/-- The two disjoint marker sectors retain their exact original weights.
The S3 sector's model still uses the entire physical S3 action. -/
theorem oddCriticalSubgroups_card (R : ℕ) (hR : 0 < R) :
    (Nat.card (OddCriticalSubgroups R) : ℚ) =
      ((2 * R + 1).factorial : ℚ) *
        ((∑ p : (criticalProfiles R), p.1.weight * Nat.card (OddCriticalModelSubgroups false p.1)) +
          (∑ p : (criticalProfiles (R - 1)), p.1.weight * Nat.card (OddCriticalModelSubgroups true p.1)) / 6) := by
  rw [oddCriticalSubgroups_card_indexed]
  congr 1
  rw [Fintype.sum_sum_type]
  simp only [oddCriticalIndexPair, Bool.false_eq_true, ↓reduceIte, div_one]
  congr 1
  let e : {p : (criticalProfiles (R - 1)) // 0 < R} ≃ (criticalProfiles (R - 1)) :=
    { toFun := Subtype.val
      invFun := fun p ↦ ⟨p,hR⟩
      left_inv := fun p ↦ Subtype.ext rfl
      right_inv := fun _ ↦ rfl }
  rw [Finset.sum_div]
  have hsum := e.sum_comp (fun p : (criticalProfiles (R - 1)) ↦
    p.1.weight * (Nat.card (OddCriticalModelSubgroups true p.1) : ℚ) / 6)
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro p _
  dsimp [e]
  ring

theorem oddCriticalSubgroups_card_le_subgroupCount (R : ℕ) :
    Nat.card (OddCriticalSubgroups R) ≤ subgroupCount (2 * R + 1) :=
  Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

end SymmetricSubgroupAsymptotics
