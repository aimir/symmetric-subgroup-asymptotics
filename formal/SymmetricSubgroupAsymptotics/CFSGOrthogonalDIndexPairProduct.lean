import SymmetricSubgroupAsymptotics.CFSGAlternatingPairOperator

/-! Exact products of original rank-two pair operators with a shared
vector. The retained cross term distinguishes a singular 3-space from
mere commutation, including in characteristic two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPairProduct
open CFSGAlternatingPairOperator
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem pairOperator_second_linear (B : LinearMap.BilinForm K V)
    (u v w : V) (a b : K) :
    pairOperator B u (a • v + b • w) = a • pairOperator B u v + b • pairOperator B u w := by
  apply LinearMap.ext
  intro x
  simp only [pairOperator_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  module

theorem pairOperator_shared_comp (B : LinearMap.BilinForm K V) (u v w : V)
    (huu : B u u = 0) (hvu : B v u = 0) (huw : B u w = 0) :
    (pairOperator B u v).comp (pairOperator B u w) = -(B v w) • (B u).smulRight u := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, pairOperator_apply, map_sub, map_smul,
    LinearMap.smul_apply, LinearMap.smulRight_apply, huu, hvu, huw, smul_eq_mul]
  module

theorem pairOperator_shared_product (B : LinearMap.BilinForm K V) (u v w : V)
    (huu : B u u = 0) (hvu : B v u = 0) (huw : B u w = 0) (a b : K) :
    (LinearMap.id + a • pairOperator B u v).comp
        (LinearMap.id + b • pairOperator B u w) =
      LinearMap.id + pairOperator B u (a • v + b • w) -
        (a * b * B v w) • (B u).smulRight u := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    pairOperator_apply, map_add, map_sub, map_smul, huu, hvu, huw, smul_eq_mul]
  module

theorem pairOperator_shared_product_of_orthogonal (B : LinearMap.BilinForm K V)
    (u v w : V) (huu : B u u = 0) (hvu : B v u = 0) (huw : B u w = 0)
    (hvw : B v w = 0) (a b : K) :
    (LinearMap.id + a • pairOperator B u v).comp
        (LinearMap.id + b • pairOperator B u w) =
      LinearMap.id + pairOperator B u (a • v + b • w) := by
  rw [pairOperator_shared_product B u v w huu hvu huw a b, hvw, mul_zero, zero_smul, sub_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPairProduct
