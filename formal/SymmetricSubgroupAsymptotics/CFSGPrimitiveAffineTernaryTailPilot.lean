import SymmetricSubgroupAsymptotics.PrimitiveAffineLinearOrderDivisor
import Mathlib.Tactic.NormNum

/-! A selected three-row pilot for the bounded prime-power tail arithmetic.
No extension to the full bounded parameter set is claimed here. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineTernaryTailPilot

theorem selected_receipt :
    20*((fullAffineOrder 2 6).factorization 3 - (2^6).factorization 3) < 3*2^6 ∧
    20*((fullAffineOrder 3 4).factorization 3 - (3^4).factorization 3) < 3*3^4 ∧
    20*((fullAffineOrder 31 2).factorization 3 - (31^2).factorization 3) < 3*31^2 := by
  unfold fullAffineOrder fullLinearOrder
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineTernaryTailPilot
