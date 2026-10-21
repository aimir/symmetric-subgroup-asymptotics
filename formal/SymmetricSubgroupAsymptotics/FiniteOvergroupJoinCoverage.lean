import SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionAbove

/-! A fixed seed and a small literal join table suffice for complete
overgroup coverage. All seed adjunctions are exact equalities of actual
subgroups; the local join table introduces no abstract group recognition. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionCoverage

variable {G I : Type*} [Group G] [Finite G]

theorem steps_of_seed_adjunctions_and_joins (H : Subgroup G)
    (rows : I → Subgroup G) (hcontain : ∀ i, H ≤ rows i)
    (hadjoin : ∀ g : G, ∃ j, H ⊔ Subgroup.closure {g} = rows j)
    (hjoin : ∀ i j, ∃ k, rows i ⊔ rows j = rows k) :
    ∀ i : I, ∀ g : G, ∃ j : I, ∃ c : G,
      MulAut.conj c • (rows i ⊔ Subgroup.closure {g}) = rows j := by
  intro i g
  obtain ⟨j, hj⟩ := hadjoin g
  obtain ⟨k, hk⟩ := hjoin i j
  have he : rows i ⊔ Subgroup.closure {g} = rows i ⊔ rows j := by
    rw [← hj, ← sup_assoc, sup_eq_left.mpr (hcontain i)]
  exact ⟨k, 1, by simpa using he.trans hk⟩

/-- The supplied row for H, exact seed-adjunction list and exact finite join
table prove coverage of every actual subgroup above H. -/
theorem complete_above_of_seed_adjunctions_and_joins (H : Subgroup G)
    (rows : I → Subgroup G) (hcontain : ∀ i, H ≤ rows i)
    (hbase : ∃ i, rows i = H)
    (hadjoin : ∀ g : G, ∃ j, H ⊔ Subgroup.closure {g} = rows j)
    (hjoin : ∀ i j, ∃ k, rows i ⊔ rows j = rows k)
    {U : Subgroup G} (hHU : H ≤ U) : Covered rows U := by
  obtain ⟨i, hi⟩ := hbase
  have hH : Covered rows H := ⟨i, 1, by simpa using hi.symm⟩
  exact complete_above rows
    (steps_of_seed_adjunctions_and_joins H rows hcontain hadjoin hjoin) hH hHU

end SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionCoverage

end
