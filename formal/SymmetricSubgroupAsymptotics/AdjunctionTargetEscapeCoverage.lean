import SymmetricSubgroupAsymptotics.FiniteLeftCosetAdjunctionCoverage

/-! If every one-element adjunction either lies in a fixed actual subgroup
or contains an upward-closed escape witness, the same holds for every
actual overgroup. No finite subgroup classification or normality is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AdjunctionTargetEscapeCoverage
variable {G : Type*} [Group G]

theorem complete (H Target : Subgroup G) (Escape : Subgroup G → Prop)
    (hmono : ∀ V W, V ≤ W → Escape V → Escape W)
    (hadjoin : ∀ g : G,
      H ⊔ Subgroup.closure {g} ≤ Target ∨ Escape (H ⊔ Subgroup.closure {g}))
    (U : Subgroup G) (hHU : H ≤ U) : U ≤ Target ∨ Escape U := by
  classical
  by_cases hle : U ≤ Target
  · exact Or.inl hle
  · right
    obtain ⟨g,hgU,hgTarget⟩ := Set.not_subset.mp hle
    rcases hadjoin g with hsmall | hescape
    · have hg : g ∈ H ⊔ Subgroup.closure {g} :=
        (show Subgroup.closure {g} ≤ H ⊔ Subgroup.closure {g} from le_sup_right)
          (Subgroup.subset_closure (by simp))
      exact (hgTarget (hsmall hg)).elim
    · apply hmono _ U _ hescape
      refine sup_le hHU ((Subgroup.closure_le U).mpr ?_)
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hgU

end SymmetricSubgroupAsymptotics.AdjunctionTargetEscapeCoverage
end
