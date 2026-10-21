import Mathlib.Algebra.Group.Subgroup.Ker

/-! Literal generators of a faithful image lift to a generating tuple
of the same original source. No replacement source group is selected. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem exists_actual_generating_tuple_of_injective_image
    {G H J : Type} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (t : J → H)
    (hgen : f.range = Subgroup.closure (Set.range t)) :
    ∃ u : J → G, (∀ i, f (u i) = t i) ∧ Subgroup.closure (Set.range u) = ⊤ := by
  have hlift : ∀ i, ∃ u, f u = t i := by
    intro i
    have hm : t i ∈ f.range := by
      rw [hgen]
      exact Subgroup.subset_closure ⟨i,rfl⟩
    exact hm
  choose u hu using hlift
  refine ⟨u,hu,?_⟩
  let C := Subgroup.closure (Set.range u)
  have hle : Subgroup.closure (Set.range t) ≤ C.map f := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨u i,Subgroup.subset_closure ⟨i,rfl⟩,hu i⟩
  apply top_unique
  intro g _
  have hg : f g ∈ C.map f := hle (hgen ▸ (show f g ∈ f.range from ⟨g,rfl⟩))
  obtain ⟨a,ha,he⟩ := hg
  exact hf he ▸ ha

end SymmetricSubgroupAsymptotics
