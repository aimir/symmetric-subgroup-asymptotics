import Mathlib.Algebra.Group.Subgroup.Ker

/-! Lifts of generators of a literal homomorphism image generate the
original group together with that homomorphism's own kernel. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.RelativeProjectionGeneratorLifts

variable {G Q : Type*} [Group G] [Group Q] (f : G →* Q)

theorem closure_lifts {l : ℕ} (a : Fin l → G)
    (hgen : Subgroup.closure (Set.range (fun i => f (a i))) = f.range) :
    Subgroup.closure (Set.range a ∪ f.ker) = ⊤ := by
  let H := Subgroup.closure (Set.range a ∪ f.ker)
  have hk : f.ker ≤ H := fun x hx => Subgroup.subset_closure (Or.inr hx)
  have hi : Subgroup.closure (Set.range (fun i => f (a i))) ≤ H.map f := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨a i, Subgroup.subset_closure (Or.inl ⟨i, rfl⟩), rfl⟩
  rw [hgen] at hi
  apply top_unique
  intro x _
  have hx : x ∈ (H.map f).comap f := hi ⟨x, rfl⟩
  rwa [Subgroup.comap_map_eq_self hk] at hx

/-- A fixed-length tuple in the actual image lifts with the same length.
The retained kernel is independent of the chosen preimages. -/
theorem exists_lifts {l : ℕ} (a : Fin l → f.range)
    (hgen : Subgroup.closure (Set.range a) = ⊤) :
    ∃ t : Fin l → G, (∀ i, f (t i) = a i) ∧
      Subgroup.closure (Set.range t ∪ f.ker) = ⊤ := by
  choose t ht using fun i => (a i).property
  refine ⟨t, ht, closure_lifts f t ?_⟩
  have hm := congrArg (Subgroup.map f.range.subtype) hgen
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hm
  have he : f.range.subtype '' Set.range a = Set.range (fun i => f (t i)) := by
    ext q
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, ht i⟩
    · rintro ⟨i, rfl⟩
      exact ⟨a i, ⟨i, rfl⟩, (ht i).symm⟩
  rwa [he] at hm

end SymmetricSubgroupAsymptotics.RelativeProjectionGeneratorLifts
end
