import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-! The remaining three higher binary unitary class-equation budgets.
This is arithmetic only. Actual original proper-index, order, outer
order and least-index-square statements must be supplied by their
proved model theorems in the consumer. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.UnitaryHigherBinaryClassEquationNumerics

def coupledBase (r : ℕ) : ℕ := 6*2^(2*r-5)

theorem coupledBase_ge_three (r : ℕ) : 3 ≤ coupledBase r := by
  have h : 1 ≤ 2^(2*r-5) := Nat.one_le_pow _ _ (by decide)
  unfold coupledBase
  omega

theorem class_equation_capacity (r : ℕ) (hr : r=4 ∨ r=5 ∨ r=6) :
    ((2^((r+1)*(r+2))/coupledBase r+1)*(2*(r+1)))^3 ≤
      5^(coupledBase r-1) := by
  rcases hr with rfl | rfl | rfl <;> decide +kernel

end SymmetricSubgroupAsymptotics.UnitaryHigherBinaryClassEquationNumerics
