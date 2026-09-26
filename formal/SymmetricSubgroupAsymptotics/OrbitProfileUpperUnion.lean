import SymmetricSubgroupAsymptotics.OrbitProfileUpperWeights

/-! An upper bound for a finite union of original physical profiles.
The actual subgroup is recovered by forgetting the chosen profile. This
map is onto even when profiles overlap, so no action-separation or unique
presentation hypothesis is needed for the upper bound. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- Every member of the physical union has at least one original profile.
Possible multiple presentations only enlarge the upper counting sum. -/
theorem assembledOrbitProfilesOn_card_le_sum
    {τ ι X : Type*} [Fintype τ] [Finite X] {Ω : ι → Type*}
    (m : τ → ι → ℕ)
    (P : ∀ t, Subgroup (Equiv.Perm (OrbitProfilePoints Ω (m t))) → Prop) :
    Nat.card (AssembledOrbitProfilesOn m P X) ≤
      ∑ t, Nat.card (AssembledOrbitProfileOn (P t) X) := by
  classical
  letI : ∀ t, Finite (AssembledOrbitProfileOn (P t) X) := fun t => by
    unfold AssembledOrbitProfileOn
    infer_instance
  let f : (Σ t, AssembledOrbitProfileOn (P t) X) → AssembledOrbitProfilesOn m P X :=
    fun H => ⟨H.2.1, H.1, H.2.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨H, t, ht⟩
    exact ⟨⟨t, ⟨H, ht⟩⟩, rfl⟩
  calc
    _ ≤ Nat.card (Σ t, AssembledOrbitProfileOn (P t) X) :=
      Nat.card_le_card_of_surjective f hf
    _ = _ := Nat.card_sigma

/-- Each profile keeps its original normalizers and occurrence factorials.
Naturality is required for that profile's full joint model predicate. -/
theorem assembledOrbitProfilesOn_fin_card_le_real
    {τ ι : Type*} [Fintype τ] [Fintype ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (m : τ → ι → ℕ) (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))
    (P : ∀ t, Subgroup (Equiv.Perm (OrbitProfilePoints Ω (m t))) → Prop)
    (n : ℕ) (hn : ∀ t, ∑ i, m t i * Fintype.card (Ω i) = n)
    (hnatural : ∀ t, OrbitProfileFamilyNatural Ω (m t) U (P t)) :
    (Nat.card (AssembledOrbitProfilesOn m P (Fin n)) : ℝ) ≤
      (n.factorial : ℝ) * ∑ t,
        (Nat.card {K // P t K} : ℝ) /
          (∏ i, (Nat.card (Subgroup.normalizer
            (U i : Set (Equiv.Perm (Ω i)))) : ℝ) ^ m t i *
              ((m t i).factorial : ℝ)) := by
  have hfirst : (Nat.card (AssembledOrbitProfilesOn m P (Fin n)) : ℝ) ≤
      ∑ t, (Nat.card (AssembledOrbitProfileOn (P t) (Fin n)) : ℝ) := by
    exact_mod_cast assembledOrbitProfilesOn_card_le_sum (X := Fin n) m P
  apply hfirst.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  have h := assembledOrbitProfileOn_card_le_real_of_model_bound
    (hnatural t) (orbitProfileFinLabels Ω (m t) n (hn t))
      (le_rfl : (Nat.card {K // P t K} : ℝ) ≤ Nat.card {K // P t K})
  rw [hn t] at h
  simpa only [mul_div_assoc] using h

end SymmetricSubgroupAsymptotics
