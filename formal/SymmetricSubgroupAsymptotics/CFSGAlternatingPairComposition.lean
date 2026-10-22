import SymmetricSubgroupAsymptotics.CFSGAlternatingPairOperator

/-! Exact composition of two skew pair operators with a shared
singular vector. This distinguishes shared-point configurations from
mutual orthogonality; commutation alone loses that distinction. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingPairOperator
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem pairOperator_comp_shared (B : LinearMap.BilinForm K V) (u v w : V)
    (huu : B u u = 0) (hvu : B v u = 0) (huw : B u w = 0) :
    (pairOperator B u v).comp (pairOperator B u w) =
      -(B v w) • (B u).smulRight u := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, pairOperator_apply, map_sub, map_smul,
    LinearMap.smul_apply, LinearMap.smulRight_apply, huu, hvu, huw,
    smul_zero, zero_smul, sub_zero, zero_sub]
  module

theorem pairOperator_comp_eq_zero_of_orthogonal (B : LinearMap.BilinForm K V) (u v w : V)
    (huu : B u u = 0) (hvu : B v u = 0) (huw : B u w = 0) (hvw : B v w = 0) :
    (pairOperator B u v).comp (pairOperator B u w) = 0 := by
  rw [pairOperator_comp_shared B u v w huu hvu huw, hvw, neg_zero, zero_smul]

theorem pairOperator_commute_shared (B : LinearMap.BilinForm K V) (u v w : V)
    (huu : B u u = 0) (hvu : B v u = 0) (huw : B u w = 0)
    (hwu : B w u = 0) (huv : B u v = 0) (hvw : B v w = B w v) :
    (pairOperator B u v).comp (pairOperator B u w) =
      (pairOperator B u w).comp (pairOperator B u v) := by
  rw [pairOperator_comp_shared B u v w huu hvu huw,
    pairOperator_comp_shared B u w v huu hwu huv, hvw]

end SymmetricSubgroupAsymptotics.CFSGAlternatingPairOperator
