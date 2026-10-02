import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Data.Fintype.Basic

/-! # A finite direct-product chart for a semisimple normal subgroup -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- A group whose center is trivial. -/
def IsCenterless (G : Type*) [Group G] : Prop :=
  ∀ x : G, (∀ y : G, x * y = y * x) → x = 1

/-- A subgroup presented as a finite direct product of centerless simple
groups.  Normality in an ambient group is deliberately kept separate. -/
structure SemisimpleNormalChart {U : Type*} [Group U] (E : Subgroup U) where
  ι : Type
  [fintype : Fintype ι]
  factor : ι → Type
  [group : ∀ i, Group (factor i)]
  [finite : ∀ i, Finite (factor i)]
  simple : ∀ i, IsSimpleGroup (factor i)
  centerless : ∀ i, IsCenterless (factor i)
  equiv : E ≃* ((i : ι) → factor i)

attribute [instance] SemisimpleNormalChart.fintype SemisimpleNormalChart.group
  SemisimpleNormalChart.finite

end SymmetricSubgroupAsymptotics

end
