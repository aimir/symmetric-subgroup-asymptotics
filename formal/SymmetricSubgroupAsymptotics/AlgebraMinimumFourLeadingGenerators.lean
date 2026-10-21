import SymmetricSubgroupAsymptotics.LeadingTermMinimumActualOrbits
import SymmetricSubgroupAsymptotics.FiniteModulePaddedGenerators

/-! When four module generators are necessary, a minimum-weight padded
tuple has four nonzero distinct leading labels and retains the complete
actual-operator noncancellation property. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
variable {k A M : Type} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    {n : ℕ}

theorem exists_minimum_four_nonzero_generators_no_collision
    (hd : ModuleGeneratedBy A M 4) (C : M →ₗ[k] (Fin n → k))
    (hC : Function.Injective C) (a0 : Fin n)
    (hneed : ∀ S : Finset M, Submodule.span A (S : Set M) = ⊤ → 4 ≤ S.card) :
    ∃ (v : Fin 4 → M) (label : Fin 4 → Fin n),
      Submodule.span A (Set.range v) = ⊤ ∧
      (∀ i, v i ≠ 0 ∧ FiniteRowLeadingWeight.HasLeading (C (v i)) (label i)) ∧
      Function.Injective label ∧
      (∀ i j, i ≠ j → ∀ r : A,
        ¬FiniteRowLeadingWeight.HasLeading (C (r • v i)) (label j)) := by
  obtain ⟨v, label, hv, hlead, hcollision⟩ :=
    exists_minimum_generators_no_actual_leading_collision hd C hC a0
  let t : Finset (Fin 4) := Finset.univ.filter (fun i => v i ≠ 0)
  let S : Finset M := t.image v
  have hspan : Submodule.span A (S : Set M) = ⊤ := by
    apply top_unique
    rw [← hv]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : v i = 0
    · rw [hi]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span (Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩)
  have hfour : 4 ≤ t.card := (hneed S hspan).trans (Finset.card_image_le)
  have ht : t = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa only [Finset.card_univ, Fintype.card_fin] using hfour
  have hnonzero : ∀ i, v i ≠ 0 := by
    intro i
    have hi : i ∈ t := by rw [ht]; exact Finset.mem_univ i
    exact (Finset.mem_filter.mp hi).2
  have hc : ∀ i j, i ≠ j → ∀ r : A,
      ¬FiniteRowLeadingWeight.HasLeading (C (r • v i)) (label j) := by
    intro i j hij r
    exact hcollision i j hij (hnonzero i) (hnonzero j) r
  refine ⟨v, label, hv, fun i => ⟨hnonzero i, hlead i (hnonzero i)⟩, ?_, hc⟩
  intro i j he
  by_contra hne
  apply hc i j hne 1
  simpa only [one_smul, he] using hlead i (hnonzero i)

end SymmetricSubgroupAsymptotics
