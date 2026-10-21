import SymmetricSubgroupAsymptotics.FiniteSeedJoinEscapeCoverage

/-! Finite low-row closure with an arbitrary upward-closed escape property.
Callers prove that property for actual adjunctions and joins; this theorem
only performs the finite maximal-row argument. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.FiniteSeedJoinEscapePropertyCoverage

variable {G I : Type*} [Group G]

theorem complete_above [Finite G] (H : Subgroup G) (Escape : Subgroup G → Prop)
    (hmono : ∀ U V : Subgroup G, U ≤ V → Escape U → Escape V)
    (rows : I → Subgroup G) (hcontain : ∀ i, H ≤ rows i) (hbase : ∃ i, rows i = H)
    (hadjoin : ∀ g : G, (∃ i, H ⊔ Subgroup.closure {g} = rows i) ∨
      Escape (H ⊔ Subgroup.closure {g}))
    (hjoin : ∀ i j, (∃ k, rows i ⊔ rows j = rows k) ∨
      Escape (rows i ⊔ rows j))
    (U : Subgroup G) (hHU : H ≤ U) :
    (∃ i, U = rows i) ∨ Escape U := by
  classical
  letI : Finite (Subgroup G) := Finite.of_injective
    (fun V : Subgroup G => (V : Set G)) SetLike.coe_injective
  let S : Set (Subgroup G) := {V | (∃ i, V = rows i) ∧ V ≤ U}
  obtain ⟨i₀, hi₀⟩ := hbase
  obtain ⟨V, _, hmax⟩ := (Set.toFinite S).exists_le_maximal
    (show H ∈ S from ⟨⟨i₀, hi₀.symm⟩, hHU⟩)
  obtain ⟨i, hi⟩ := hmax.1.1
  have hVU : V ≤ U := hmax.1.2
  by_cases heq : V = U
  · exact Or.inl ⟨i, heq.symm.trans hi⟩
  · have hnot : ¬ U ≤ V := fun h => heq (le_antisymm hVU h)
    obtain ⟨g, hgU, hgV⟩ := Set.not_subset.mp hnot
    have hclosure : Subgroup.closure {g} ≤ U := (Subgroup.closure_le U).mpr (by
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hgU)
    rcases hadjoin g with ⟨j, hj⟩ | hescape
    · have hrowiU : rows i ≤ U := by rw [← hi]; exact hVU
      have hrowjU : rows j ≤ U := by rw [← hj]; exact sup_le hHU hclosure
      let W : Subgroup G := V ⊔ Subgroup.closure {g}
      have hW : W = rows i ⊔ rows j := by
        change V ⊔ Subgroup.closure {g} = rows i ⊔ rows j
        rw [hi, ← hj, ← sup_assoc, sup_eq_left.mpr (hcontain i)]
      rcases hjoin i j with ⟨k, hk⟩ | hescape
      · have hWU : W ≤ U := sup_le hVU hclosure
        have hWV : W ≤ V := hmax.2 ⟨⟨k, hW.trans hk⟩, hWU⟩ le_sup_left
        have hgW : g ∈ W :=
          (show Subgroup.closure {g} ≤ W from le_sup_right)
            (Subgroup.subset_closure (by simp))
        exact False.elim (hgV (hWV hgW))
      · exact Or.inr (hmono _ _ (sup_le hrowiU hrowjU) hescape)
    · exact Or.inr (hmono _ _ (sup_le hHU hclosure) hescape)

end SymmetricSubgroupAsymptotics.FiniteSeedJoinEscapePropertyCoverage

end
