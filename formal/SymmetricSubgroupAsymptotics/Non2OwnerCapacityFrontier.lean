import SymmetricSubgroupAsymptotics.Non2FirstOwnerPhysicalFrontier

/-!
# Earlier owners plus one residual capacity branch

An arbitrary finite list of earlier physical owners is extended by one final
catch-all owner.  First ownership at that last index is proved equivalent to
failure of every earlier owner.  This makes the owner-or-capacity dichotomy
literal: the final complete-source envelope is required only on the actual
unowned residual family, while every earlier branch keeps its own certificate.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Append one always-eligible residual branch to an ordered menu of earlier
physical owners. -/
def ownerOrResidualEligible {r : ℕ}
    (Earlier : ∀ n, Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (n : ℕ) (i : Fin (r+1))
    (H : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  if hi : i.val < r then Earlier n ⟨i.val, hi⟩ H else True

@[simp] theorem ownerOrResidualEligible_castSucc {r n : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (i : Fin r) (H : Subgroup (Equiv.Perm (Fin n))) :
    ownerOrResidualEligible Earlier n i.castSucc H ↔ Earlier n i H := by
  simp [ownerOrResidualEligible]

@[simp] theorem ownerOrResidualEligible_last {r n : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (H : Subgroup (Equiv.Perm (Fin n))) :
    ownerOrResidualEligible Earlier n (Fin.last r) H := by
  simp [ownerOrResidualEligible]

theorem ownerOrResidualEligible_natural {r : ℕ}
    (Earlier : ∀ n, Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier) :
    DegreeNaturalOwnerMenu (ownerOrResidualEligible Earlier) := by
  intro m n hmn e i H
  by_cases hi : i.val < r
  · simpa [ownerOrResidualEligible, hi] using
      hEarlier hmn e ⟨i.val, hi⟩ H
  · simp [ownerOrResidualEligible, hi]

theorem ownerOrResidualEligible_cover {r n : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (H : Subgroup (Equiv.Perm (Fin n))) :
    ∃ i, ownerOrResidualEligible Earlier n i H :=
  ⟨Fin.last r, ownerOrResidualEligible_last Earlier H⟩

/-- An earlier owner keeps exactly its old first-owned family after the
residual branch is appended. -/
theorem firstOwned_ownerOrResidual_castSucc_iff {r n : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (i : Fin r) (H : Subgroup (Equiv.Perm (Fin n))) :
    FirstOwned (ownerOrResidualEligible Earlier n) i.castSucc H ↔
      FirstOwned (Earlier n) i H := by
  constructor
  · rintro ⟨hi, hprior⟩
    refine ⟨(ownerOrResidualEligible_castSucc Earlier i H).mp hi, ?_⟩
    intro j hj hjEligible
    exact hprior j.castSucc (by simpa using hj)
      ((ownerOrResidualEligible_castSucc Earlier j H).mpr hjEligible)
  · rintro ⟨hi, hprior⟩
    refine ⟨(ownerOrResidualEligible_castSucc Earlier i H).mpr hi, ?_⟩
    intro j hj hjEligible
    have hjval : j.val < r := by
      have hil : i.val < r := i.isLt
      exact lt_trans hj hil
    let k : Fin r := ⟨j.val, hjval⟩
    have hki : k < i := by exact hj
    have hkEligible : Earlier n k H := by
      simpa [ownerOrResidualEligible, hjval, k] using hjEligible
    exact hprior k hki hkEligible

/-- The appended owner is first exactly on the residual states rejected by
all earlier owners. -/
theorem firstOwned_ownerOrResidual_last_iff {r n : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (H : Subgroup (Equiv.Perm (Fin n))) :
    FirstOwned (ownerOrResidualEligible Earlier n) (Fin.last r) H ↔
      ∀ i : Fin r, ¬ Earlier n i H := by
  constructor
  · intro h i hi
    exact h.2 i.castSucc (by simp)
      ((ownerOrResidualEligible_castSucc Earlier i H).mpr hi)
  · intro h
    refine ⟨ownerOrResidualEligible_last Earlier H, ?_⟩
    intro j hj hjEligible
    have hjval : j.val < r := by exact hj
    let i : Fin r := ⟨j.val, hjval⟩
    have hi : Earlier n i H := by
      simpa [ownerOrResidualEligible, hjval, i] using hjEligible
    exact h i hi

namespace RepeatedMarkerOwnerBound

/-- Earlier owners plus the residual owner cover the whole outside frontier,
with no separate exhaustiveness hypothesis. -/
theorem outsideFitsAt_ownerOrResidual_physical_cover {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier)
    (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ OutsideFitsSubgroupSetAt n) :
    ∃ j : GrowingQuotientPhysicalIndex
        (ι := fun w => Non2FirstOwnerIndex (r+1) w) 3 n,
      H ∈ GrowingQuotientCanonicalFamily 3 n
        non2FirstOwnerAction
        (non2FirstOwnerPredicate (ownerOrResidualEligible Earlier)) j :=
  outsideFitsAt_firstOwner_physical_cover
    (ownerOrResidualEligible Earlier)
    (ownerOrResidualEligible_natural Earlier hEarlier)
    (fun _ H _ => ownerOrResidualEligible_cover Earlier H) n H hH

theorem outsideFitsAt_ownerOrResidual_physicalBound_of_local {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier)
    (D : ∀ w, Non2FirstOwnerIndex (r+1) w → ℕ → ℝ)
    (A : ∀ w, Non2FirstOwnerIndex (r+1) w → ℝ)
    (v : ∀ w, Non2FirstOwnerIndex (r+1) w → ℕ)
    (η δ c α : ∀ w, Non2FirstOwnerIndex (r+1) w → ℝ)
    (hlocal : GrowingQuotientLocalPhysicalBound 3 non2FirstOwnerAction
      (non2FirstOwnerPredicate (ownerOrResidualEligible Earlier))
      D A v η δ c α) :
    GrowingQuotientPhysicalBound outsideFitsAtRatio 3
      D A v η δ c α :=
  outsideFitsAt_firstOwner_physicalBound_of_local
    (ownerOrResidualEligible Earlier)
    (ownerOrResidualEligible_natural Earlier hEarlier)
    (fun _ H _ => ownerOrResidualEligible_cover Earlier H)
    D A v η δ c α hlocal

/-- Exact endgame interface.  The branch-specific complete-source envelope
is evaluated after first ownership, so its final owner is precisely the
annihilator-aware residual family. -/
noncomputable def
    outsideFrontier_exponentialForwardEstimate_of_ownerOrResidual
    {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier)
    { ρ : ℝ }
    (R : ∀ w, Non2FirstOwnerIndex (r+1) w → Type*)
    [∀ w i, Group (R w i)] [∀ w i, Finite (R w i)]
    (D : ∀ w, Non2FirstOwnerIndex (r+1) w → ℕ → ℝ)
    (A : ∀ w, Non2FirstOwnerIndex (r+1) w → ℝ)
    (v : ∀ w, Non2FirstOwnerIndex (r+1) w → ℕ)
    (η δ c α : ∀ w, Non2FirstOwnerIndex (r+1) w → ℝ)
    (ρR : ∀ w i, R w i →* Equiv.Perm (Fin (v w i)))
    (hρR : ∀ w i, Function.Injective (ρR w i))
    (hD : ∀ w i b, 0 ≤ D w i b)
    (hA : ∀ w i, A w i =
      (Nat.card (Subgroup.normalizer
        (non2FirstOwnerAction w i : Set (Equiv.Perm (Fin w)))) : ℝ))
    (hα : ∀ w i, α w i = η w i + c w i)
    (henvelope : ∀ w i b (J : Subgroup (Equiv.Perm (Fin b))),
      fusionCompleteSourceSum (non2FirstOwnerAction w i)
          (non2FirstOwnerPredicate (ownerOrResidualEligible Earlier) w i b) J ≤
        (D w i b * (2 : ℝ) ^ (η w i * b)) *
          completeQuotientWeight (R := R w i) J)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    (hp : GrowingQuotientParameterBound ρ v η δ c α)
    (hmass : GrowingMenuMassBound 3 D A)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      OrdinaryFrontierClosure.outsideFrontierRatio := by
  let Eligible := ownerOrResidualEligible Earlier
  have hEligible : DegreeNaturalOwnerMenu Eligible :=
    ownerOrResidualEligible_natural Earlier hEarlier
  have hP : ∀ w i b, FusionOrbitNatural (non2FirstOwnerAction w i)
      (non2FirstOwnerPredicate Eligible w i b) := by
    intro w i b
    apply non2FirstOwnerPredicate_natural
    intro n j s H
    exact hEligible rfl s j H
  have hlocal : GrowingQuotientLocalPhysicalBound 3 non2FirstOwnerAction
      (non2FirstOwnerPredicate Eligible) D A v η δ c α :=
    growingQuotientLocalPhysicalBound_of_completeSource 3
      non2FirstOwnerAction (non2FirstOwnerPredicate Eligible)
      R D A v η δ c α ρR hρR hP hD hA hα henvelope
  exact outsideFrontier_exponentialForwardEstimate_of_non2FirstOwner
    Eligible hEligible (fun _ H _ => ownerOrResidualEligible_cover Earlier H)
      D A v η δ c α hρ hρ8 hD
      (fun w i => by
        rw [hA w i]
        exact_mod_cast (Nat.card_pos (α :=
          Subgroup.normalizer
            (non2FirstOwnerAction w i : Set (Equiv.Perm (Fin w))))))
      hp hmass hcoarse hlocal

end RepeatedMarkerOwnerBound
end SymmetricSubgroupAsymptotics

end
