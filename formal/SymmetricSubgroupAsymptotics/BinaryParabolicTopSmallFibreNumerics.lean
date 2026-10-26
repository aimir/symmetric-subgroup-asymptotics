import SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryParabolicClassBound

/-! The binary estimates use the proved SAME-action unsigned motion
reserve. The naked coordinate/class product is not asserted to pay. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.BinaryParabolicTopSmallFibreNumerics
open PrimitiveAffineBinaryParabolicClassBound

theorem classBudget_ge_eleven (n : ℕ) : 11 ≤ classBudget n := by
  unfold classBudget
  split_ifs <;> decide

theorem binary_unsigned_capacity (n : ℕ) (hn : n=8 ∨ n=16 ∨ n=32) :
    ((classBudget n+1)*2^(n-2))^3 ≤ 5^(2*n-1) := by
  rcases hn with rfl|rfl|rfl <;> unfold classBudget <;> decide +kernel

theorem ternary_capacity (n : ℕ) (hn : n=8 ∨ n=16 ∨ n=32) :
    (3^n*classBudget n)^3 ≤ 5^(3*n-1) := by
  rcases hn with rfl|rfl|rfl <;> unfold classBudget <;> decide +kernel

theorem affine_order_lt_factorial (n : ℕ) (hn : n=8 ∨ n=16 ∨ n=32) :
    n*n^Nat.log 2 n < n.factorial := by
  rcases hn with rfl|rfl|rfl <;> decide +kernel

end SymmetricSubgroupAsymptotics.BinaryParabolicTopSmallFibreNumerics
