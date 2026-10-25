import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! The proved binary-product slack gives a strict primitive class
cube. A one-power saving in each actual component pays a top of size
two or three without any independence assumption on the block kernel. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.LargePrimitiveSubnormalGapNumerics

theorem five_pow_succ_le_eight_pow (n : ℕ) (hn : 4 ≤ n) :
    5 ^ (n + 1) ≤ 8 ^ n := by
  induction n,hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    calc
      5 ^ (n + 1 + 1) = 5 ^ (n + 1) * 5 := pow_succ _ _
      _ ≤ 8 ^ n * 8 := Nat.mul_le_mul ih (by decide)
      _ = 8 ^ (n + 1) := (pow_succ _ _).symm

theorem cube_gap_of_binary_product (n x : ℕ) (hn : 4 ≤ n)
    (h : (2 ^ n * x) ^ 3 ≤ 5 ^ (2 * n - 1)) : x ^ 3 ≤ 5 ^ (n - 2) := by
  have h8 : (8 : ℕ) ^ n = (2 ^ n) ^ 3 := by
    simp only [show (8 : ℕ) = 2 ^ 3 by decide,← pow_mul,Nat.mul_comm]
  have hp : 5 ^ (n + 1) * x ^ 3 ≤ 5 ^ (n + 1) * 5 ^ (n - 2) := by
    calc
      _ ≤ 8 ^ n * x ^ 3 := Nat.mul_le_mul_right _ (five_pow_succ_le_eight_pow n hn)
      _ = (2 ^ n * x) ^ 3 := by rw [h8,mul_pow]
      _ ≤ 5 ^ (2 * n - 1) := h
      _ = _ := by rw [← pow_add]; congr 1; omega
  exact Nat.le_of_mul_le_mul_left hp (pow_pos (by decide : 0 < (5 : ℕ)) _)

theorem small_top_cube_of_gap (a b x : ℕ) (ha : 2 ≤ a) (hb : b = 2 ∨ b = 3)
    (hx : x ^ 3 ≤ 5 ^ (a - 2)) :
    (x ^ b * b) ^ 3 ≤ 5 ^ (a * b - 1) := by
  have ht : b ^ 3 ≤ 5 ^ (2 * b - 1) := by rcases hb with rfl | rfl <;> decide +kernel
  calc
    _ = (x ^ 3) ^ b * b ^ 3 := by
      rw [mul_pow,← pow_mul,← pow_mul,Nat.mul_comm b 3]
    _ ≤ (5 ^ (a - 2)) ^ b * 5 ^ (2 * b - 1) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hx b) ht
    _ = _ := by
      rw [← pow_mul,← pow_add]
      congr 1
      rcases hb with rfl | rfl <;> omega

end SymmetricSubgroupAsymptotics.LargePrimitiveSubnormalGapNumerics
