import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! A cyclic original group has normally cyclic socles in every quotient.
This uses ordinary cyclic-subgroup generation and no subgroup census. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

theorem normal_generating_singletons_of_isCyclic
    {G : Type} [Group G] [IsCyclic G] :
    ∀ N : Subgroup G, N.Normal →
      ∃ x : Fin 1 → G, Subgroup.normalClosure (Set.range x) = N := by
  intro N hN
  letI := hN
  obtain ⟨g, hg⟩ := N.isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic N)
  refine ⟨fun _ ↦ g, ?_⟩
  have hrange : Set.range (fun _ : Fin 1 ↦ g) = {g} := by ext x; simp
  rw [hrange]
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [← hg]
    exact Subgroup.mem_zpowers g
  · rw [← hg, Subgroup.zpowers_eq_closure]
    exact Subgroup.closure_le_normalClosure

theorem quotientSocle_one_of_isCyclic
    {G : Type} [Group G] [IsCyclic G]
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 1 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    normal_generating_singletons_of_isCyclic N

end SymmetricSubgroupAsymptotics
end
