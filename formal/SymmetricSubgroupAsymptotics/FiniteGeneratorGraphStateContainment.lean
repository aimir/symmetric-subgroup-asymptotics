import SymmetricSubgroupAsymptotics.FiniteGeneratorGraphInjection

/-! Reuse a checked graph with a different exact original generator alphabet. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteGeneratorGraphCertificate
variable {G H K I J L : Type} [Group G] [Group H] [Group K]
  {source : J → G} {target : J → H}
  (C : FiniteGeneratorGraphCertificate (I := I) source target)

theorem state_mem_graph (i : I) : C.state i ∈ C.graph := by
  rw [← C.word_eq i]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure (Set.mem_range_self j)

theorem first_comp_injective_of_generated_states
    (f : K →* G × H) (hf : Function.Injective f) (g : L → K)
    (hg : Subgroup.closure (Set.range g) = ⊤)
    (hfg : ∀ l, ∃ i, f (g l) = C.state i) :
    Function.Injective ((MonoidHom.fst G H).comp f) := by
  apply C.first_comp_injective f hf
  have hle : Subgroup.closure (Set.range g) ≤ C.graph.comap f := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨l, rfl⟩
    change f (g l) ∈ C.graph
    obtain ⟨i, hi⟩ := hfg l
    rw [hi]
    exact C.state_mem_graph i
  rw [hg] at hle
  exact fun k => hle (Subgroup.mem_top k)
end SymmetricSubgroupAsymptotics.FiniteGeneratorGraphCertificate
