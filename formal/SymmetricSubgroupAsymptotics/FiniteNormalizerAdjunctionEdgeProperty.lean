import SymmetricSubgroupAsymptotics.FiniteNormalizerAdjunctionProperty

/-! A finite selected normalizer action table suffices for forest
transport. Invariance under the full ambient normalizer is not required. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.FiniteNormalizerAdjunctionReduction

variable {G : Type*} [Group G] {H : Subgroup G} {q r : ℕ}
  {representatives : Fin q → G}
  (D : FiniteNormalizerAdjunctionReduction H representatives r)

theorem edge_property_representative (property : Subgroup G → Prop)
    (hedge : ∀ i hi, ∀ U : Subgroup G, property U →
      property (MulAut.conj (D.conjugator i hi) • U))
    (hroot : ∀ k : Fin r, property
      (H ⊔ Subgroup.closure {representatives (D.roots k)})) (i : Fin q) :
    property (H ⊔ Subgroup.closure {representatives i}) := by
  by_cases hi : i = D.roots (D.label i)
  · rw [hi]
    exact hroot _
  · rw [← D.edge_conjugated i hi]
    exact hedge i hi _
      (edge_property_representative property hedge hroot (D.parent i hi))
termination_by D.rank i
decreasing_by exact D.parent_lt i hi

end SymmetricSubgroupAsymptotics.FiniteNormalizerAdjunctionReduction

end
