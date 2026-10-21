import SymmetricSubgroupAsymptotics.SeedAdjunctionLargerSubgroup

/-! Exact low-row joins with escape to a previously classified larger
seed. Only the low rows need a join table; larger adjunctions and joins
are certified by actual subgroup inclusions. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics

variable {G I : Type*} [Group G] [Finite G]

theorem complete_above_of_seed_joins_or_larger
    (H K : Subgroup G) (rows : I → Subgroup G)
    (hcontain : ∀ i, H ≤ rows i) (hbase : ∃ i, rows i = H)
    (hadjoin : ∀ g : G, (∃ i, H ⊔ Subgroup.closure {g} = rows i) ∨
      ∃ c : G, MulAut.conj c • K ≤ H ⊔ Subgroup.closure {g})
    (hjoin : ∀ i j, (∃ k, rows i ⊔ rows j = rows k) ∨
      ∃ c : G, MulAut.conj c • K ≤ rows i ⊔ rows j)
    (U : Subgroup G) (hHU : H ≤ U) :
    (∃ i, U = rows i) ∨ ∃ c : G, MulAut.conj c • K ≤ U := by
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
    rcases hadjoin g with ⟨j, hj⟩ | ⟨c, hc⟩
    · have hrowiU : rows i ≤ U := by rw [← hi]; exact hVU
      have hrowjU : rows j ≤ U := by rw [← hj]; exact sup_le hHU hclosure
      let W : Subgroup G := V ⊔ Subgroup.closure {g}
      have hW : W = rows i ⊔ rows j := by
        change V ⊔ Subgroup.closure {g} = rows i ⊔ rows j
        rw [hi, ← hj, ← sup_assoc, sup_eq_left.mpr (hcontain i)]
      rcases hjoin i j with ⟨k, hk⟩ | ⟨c, hc⟩
      · have hWU : W ≤ U := sup_le hVU hclosure
        have hWV : W ≤ V := hmax.2 ⟨⟨k, hW.trans hk⟩, hWU⟩ le_sup_left
        have hgW : g ∈ W :=
          (show Subgroup.closure {g} ≤ W from le_sup_right)
            (Subgroup.subset_closure (by simp))
        exact False.elim (hgV (hWV hgW))
      · exact Or.inr ⟨c, hc.trans (sup_le hrowiU hrowjU)⟩
    · exact Or.inr ⟨c, hc.trans (sup_le hHU hclosure)⟩

end SymmetricSubgroupAsymptotics

end
