import SymmetricSubgroupAsymptotics.PrimitiveAffineLinearOrderDivisor

/-! A selected full-valuation arithmetic pilot for the actual chief-weight
  tail. Unlike the relative-head pilot, no translation debt is subtracted. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGPrimitiveChiefWeightTailPilot

theorem selected_receipt :
    10*(fullAffineOrder 2 6).factorization 3 ≤ 3*2^6 ∧
    10*(fullAffineOrder 3 4).factorization 3 ≤ 3*3^4 ∧
    10*(fullAffineOrder 31 2).factorization 3 ≤ 3*31^2 := by
  unfold fullAffineOrder fullLinearOrder
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGPrimitiveChiefWeightTailPilot
