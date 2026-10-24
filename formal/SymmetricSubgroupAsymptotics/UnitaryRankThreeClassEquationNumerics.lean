import Mathlib.Data.Nat.Basic

/-! Two exact class-equation division budgets for the original unitary
rank-three models. These arithmetic inequalities assert no index bound. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.UnitaryRankThreeClassEquationNumerics

theorem binary_capacity : ((655360 / 24 + 1) * 8 : ℕ)^3 ≤ 5^(24-1) := by
  decide +kernel

theorem ternary_capacity : (((3^20 / 48 + 1) * 8 : ℕ))^3 ≤ 5^(48-1) := by
  decide +kernel

end SymmetricSubgroupAsymptotics.UnitaryRankThreeClassEquationNumerics
