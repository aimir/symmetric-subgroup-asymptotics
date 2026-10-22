import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndex

/-! Exact cardinal consequences for the SAME original finite matrix
subgroups. No order formula or named classical-group identification is
used; subgroup cardinality times the checked literal index suffices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexCardinality
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexComponentMatrices CFSGOrthogonalDIndexRootComponents
open CFSGOrthogonalDIsometryIndexComponents CFSGOrthogonalDIsometryIndex
variable (K : Type) [Field K] [Finite K]

theorem component_card_le_two_mul_elementary (s : ℕ) :
    Nat.card (componentMatrices K (s + 4)) ≤ 2 * Nat.card (elementaryRootGroup K (s + 4)) := by
  let H := (elementaryRootGroup K (s + 4)).subgroupOf (componentMatrices K (s + 4))
  have hcard : Nat.card H = Nat.card (elementaryRootGroup K (s + 4)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (elementary_le_componentMatrices K s)).toEquiv
  calc
    Nat.card (componentMatrices K (s + 4)) = Nat.card H * H.index := H.card_mul_index.symm
    _ ≤ Nat.card H * 2 := Nat.mul_le_mul_left _ (elementary_component_index_le_two K s)
    _ = _ := by rw [hcard, Nat.mul_comm]

theorem quadratic_card_le_four_mul_elementary (s : ℕ) :
    Nat.card (quadraticPreserving K (s + 4)) ≤ 4 * Nat.card (elementaryRootGroup K (s + 4)) := by
  let H := (elementaryRootGroup K (s + 4)).subgroupOf (quadraticPreserving K (s + 4))
  have hcard : Nat.card H = Nat.card (elementaryRootGroup K (s + 4)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (elementary_le_quadraticPreserving K s)).toEquiv
  calc
    Nat.card (quadraticPreserving K (s + 4)) = Nat.card H * H.index := H.card_mul_index.symm
    _ ≤ Nat.card H * 4 := Nat.mul_le_mul_left _ (elementary_quadratic_isometry_index_le_four K s)
    _ = _ := by rw [hcard, Nat.mul_comm]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexCardinality
