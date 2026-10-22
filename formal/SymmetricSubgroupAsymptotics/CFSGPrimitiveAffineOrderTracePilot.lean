import SymmetricSubgroupAsymptotics.PrimitiveAffineLinearOrderDivisor
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! A selected prime-factor order-budget pilot, with no group census. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineOrderTracePilot

theorem selected_GL_two_seven : ArithmeticFunction.cardFactors (fullLinearOrder 7 2)=8 := by
  unfold fullLinearOrder
  decide +kernel

theorem selected_GL_four_three : ArithmeticFunction.cardFactors (fullLinearOrder 3 4)=17 := by
  unfold fullLinearOrder
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineOrderTracePilot
