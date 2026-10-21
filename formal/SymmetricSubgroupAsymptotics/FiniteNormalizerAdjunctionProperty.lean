import SymmetricSubgroupAsymptotics.FiniteNormalizerAdjunctionCoverage

/-! The same checked normalizer forest transports any seed-normalizer
invariant subgroup property, including the existence of a larger actual
binary subgroup. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.FiniteNormalizerAdjunctionReduction

variable {G : Type*} [Group G] {H : Subgroup G} {q r : ℕ}
  {representatives : Fin q → G}
  (D : FiniteNormalizerAdjunctionReduction H representatives r)

theorem property_representative (property : Subgroup G → Prop)
    (hconjugate : ∀ c : G, MulAut.conj c • H = H → ∀ U : Subgroup G,
      property U → property (MulAut.conj c • U))
    (hroot : ∀ k : Fin r, property
      (H ⊔ Subgroup.closure {representatives (D.roots k)})) (i : Fin q) :
    property (H ⊔ Subgroup.closure {representatives i}) := by
  by_cases hi : i = D.roots (D.label i)
  · rw [hi]
    exact hroot _
  · rw [← D.edge_conjugated i hi]
    exact hconjugate (D.conjugator i hi) (D.conjugates_seed i hi) _
      (property_representative property hconjugate hroot (D.parent i hi))
termination_by D.rank i
decreasing_by exact D.parent_lt i hi

end SymmetricSubgroupAsymptotics.FiniteNormalizerAdjunctionReduction

end
