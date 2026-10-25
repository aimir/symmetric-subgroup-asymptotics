import Mathlib.Tactic

/-! The full original component order and outer-order charge at q=8.
This finite arithmetic does not supply the required proper-index bound. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.ReeFFourFieldEightClassNumerics

theorem component_order_cube : ((8 : ℕ)^26*3)^3 ≤ 5^(109-1) := by
  decide +kernel

theorem order_lower : 1024 ≤ (8 : ℕ)^24 := by
  decide +kernel

end SymmetricSubgroupAsymptotics.ReeFFourFieldEightClassNumerics
