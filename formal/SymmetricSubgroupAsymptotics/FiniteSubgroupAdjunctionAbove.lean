import SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionCoverage

/-! Coverage above a supplied covered seed. This is the form needed for
transitive permutation groups: a transitive Sylow subgroup supplies the
seed, and every later single-element adjunction remains transitive. -/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionCoverage

variable {G I : Type*} [Group G] [Finite G] (rows : I → Subgroup G)

theorem complete_above
    (hstep : ∀ i : I, ∀ g : G, ∃ j : I, ∃ c : G,
      MulAut.conj c • (rows i ⊔ Subgroup.closure {g}) = rows j)
    {P U : Subgroup G} (hP : Covered rows P) (hPU : P ≤ U) :
    Covered rows U := by
  classical
  letI : Finite (Subgroup G) := Finite.of_injective
    (fun V : Subgroup G => (V : Set G)) SetLike.coe_injective
  let S : Set (Subgroup G) := {V | Covered rows V ∧ V ≤ U}
  obtain ⟨V, _, hmax⟩ := (Set.toFinite S).exists_le_maximal
    (show P ∈ S from ⟨hP, hPU⟩)
  have hV : Covered rows V := hmax.1.1
  have hVU : V ≤ U := hmax.1.2
  by_cases heq : V = U
  · exact heq ▸ hV
  · have hnot : ¬ U ≤ V := fun h => heq (le_antisymm hVU h)
    obtain ⟨g, hgU, hgnV⟩ := Set.not_subset.mp hnot
    let W : Subgroup G := V ⊔ Subgroup.closure {g}
    have hW : Covered rows W := covered_adjoin rows hstep hV g
    have hWU : W ≤ U := sup_le hVU ((Subgroup.closure_le U).mpr (by
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact hgU))
    have hWV : W ≤ V := hmax.2 ⟨hW, hWU⟩ le_sup_left
    have hgW : g ∈ W :=
      (show Subgroup.closure {g} ≤ W from le_sup_right)
        (Subgroup.subset_closure (by simp))
    exact False.elim (hgnV (hWV hgW))

end SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionCoverage

end
