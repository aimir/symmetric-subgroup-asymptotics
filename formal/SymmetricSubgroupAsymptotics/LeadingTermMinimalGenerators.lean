import SymmetricSubgroupAsymptotics.SchurIsotypicGenerators

/-! The elementary reduction step behind the induced-module leading-term
argument. Minimizing a natural weight on a padded generating tuple makes
every leading-term cancellation by another generator impossible. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.LeadingTermMinimalGenerators

variable {R M : Type} [Ring R] [AddCommGroup M] [Module R M]

def replace (n : ℕ) (v : Fin n → M) (i j : Fin n) (r : R) : Fin n → M :=
  Function.update v i (v i-r • v j)

/-- An elementary row operation on the original tuple preserves its
actual generated submodule; no semisimplicity is used. -/
theorem span_replace (n : ℕ) (v : Fin n → M) (i j : Fin n) (r : R)
    (hji : j≠i) :
    Submodule.span R (Set.range (replace n v i j r))=
      Submodule.span R (Set.range v) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    by_cases hai : a=i
    · subst a
      simp only [replace,Function.update_self]
      exact (Submodule.span R (Set.range v)).sub_mem
        (Submodule.subset_span (Set.mem_range_self i))
        ((Submodule.span R (Set.range v)).smul_mem r
          (Submodule.subset_span (Set.mem_range_self j)))
    · simpa only [replace,Function.update_of_ne hai] using
        (Submodule.subset_span (Set.mem_range_self a) :
          v a∈Submodule.span R (Set.range v))
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    have hj : v j∈Submodule.span R (Set.range (replace n v i j r)) := by
      have h := (Submodule.subset_span (Set.mem_range_self j) :
        replace n v i j r j∈Submodule.span R (Set.range (replace n v i j r)))
      simpa only [replace,Function.update_of_ne hji] using h
    by_cases hai : a=i
    · subst a
      have hi := (Submodule.subset_span (Set.mem_range_self i) :
        replace n v i j r i∈Submodule.span R (Set.range (replace n v i j r)))
      simp only [replace,Function.update_self] at hi
      have h := (Submodule.span R (Set.range (replace n v i j r))).add_mem hi
        ((Submodule.span R (Set.range (replace n v i j r))).smul_mem r hj)
      simpa only [sub_add_cancel] using h
    · have h := (Submodule.subset_span (Set.mem_range_self a) :
        replace n v i j r a∈Submodule.span R (Set.range (replace n v i j r)))
      simpa only [replace,Function.update_of_ne hai] using h

/-- Any available finite generating length admits a generating tuple with
minimum total weight. The coefficient ring and module may be infinite. -/
theorem exists_minimum_weight (n : ℕ) (hn : ModuleGeneratedBy R M n)
    (weight : M → ℕ) :
    ∃ v : Fin n → M, Submodule.span R (Set.range v)=⊤ ∧
      ∀ w : Fin n → M, Submodule.span R (Set.range w)=⊤ →
        (∑ i, weight (v i))≤∑ i, weight (w i) := by
  let P : ℕ → Prop := fun a => ∃ v : Fin n → M,
    Submodule.span R (Set.range v)=⊤ ∧ (∑ i,weight (v i))=a
  have hex : ∃ a, P a := by
    obtain ⟨v,hv⟩ := hn
    exact ⟨_,v,hv,rfl⟩
  obtain ⟨v,hv,hcost⟩ := Nat.find_spec hex
  refine ⟨v,hv,?_⟩
  intro w hw
  have h := Nat.find_min' hex (show P (∑ i,weight (w i)) from ⟨w,hw,rfl⟩)
  rw [←hcost] at h
  exact h

/-- Cancellation to a strictly lower weight contradicts minimality of
the original generating tuple. -/
theorem no_lower_weight_cancellation
    (n : ℕ) (weight : M → ℕ) (v : Fin n → M)
    (hv : Submodule.span R (Set.range v)=⊤)
    (hmin : ∀ w : Fin n → M, Submodule.span R (Set.range w)=⊤ →
      (∑ i,weight (v i))≤∑ i,weight (w i))
    (i j : Fin n) (hji : j≠i) (r : R) :
    ¬ weight (v i-r • v j)<weight (v i) := by
  intro hlt
  have hgen : Submodule.span R (Set.range (replace n v i j r))=⊤ :=
    (span_replace n v i j r hji).trans hv
  have hcost : (∑ a,weight (replace n v i j r a))<∑ a,weight (v a) := by
    apply Finset.sum_lt_sum
    · intro a _
      by_cases hai : a=i
      · subst a
        simpa only [replace,Function.update_self] using hlt.le
      · simp only [replace,Function.update_of_ne hai,le_refl]
    · exact ⟨i,Finset.mem_univ i,by simpa only [replace,Function.update_self] using hlt⟩
  exact (Nat.not_lt_of_ge (hmin _ hgen)) hcost

end SymmetricSubgroupAsymptotics.LeadingTermMinimalGenerators
