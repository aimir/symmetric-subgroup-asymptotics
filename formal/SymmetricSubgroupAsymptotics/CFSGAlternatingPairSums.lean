import SymmetricSubgroupAsymptotics.CFSGAlternatingPairOperator

/-! Exact additivity in the two literal vector arguments of the skew
pair operator, used for the actual shared-point root-product identity. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingPairOperator
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem pairOperator_add_right (B : LinearMap.BilinForm K V) (u v w : V) :
    pairOperator B u (v + w) = pairOperator B u v + pairOperator B u w := by
  apply LinearMap.ext
  intro x
  simp only [pairOperator_apply, map_add, LinearMap.add_apply, smul_add, add_smul]
  module

end SymmetricSubgroupAsymptotics.CFSGAlternatingPairOperator
