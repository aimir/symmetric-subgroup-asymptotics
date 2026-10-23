import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! A base component ORDER cube pays every number of actual socle
factors in an index form. The permutation factor is retained, rather
than discarded or treated as a class-monotonicity assertion. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.ComponentOrderCubeWreathNumerics

theorem factorial_step_cube_le (k : ℕ) : (k + 1) ^ 3 ≤ 5 ^ (2 * k) := by
  calc
    (k + 1) ^ 3 ≤ (2 ^ k) ^ 3 :=
      Nat.pow_le_pow_left (Nat.succ_le_of_lt k.lt_two_pow_self) 3
    _ = ((2 : ℕ) ^ 3) ^ k := by
      rw [←pow_mul, ←pow_mul, Nat.mul_comm]
    _ ≤ ((5 : ℕ) ^ 2) ^ k := Nat.pow_le_pow_left (by decide) k
    _ = 5 ^ (2 * k) := (pow_mul 5 2 k).symm

theorem wreath_order_cube_le (A m k : ℕ) (hm : 3 ≤ m) (hk : 1 ≤ k)
    (hA : A ^ 3 ≤ 5 ^ (m - 1)) :
    (A ^ k * k.factorial) ^ 3 ≤ 5 ^ (m ^ k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => simpa only [pow_one, Nat.factorial_one, mul_one] using hA
  | succ k hk ih =>
    have hmk : k + 1 ≤ m ^ k :=
      (Nat.succ_le_of_lt k.lt_two_pow_self).trans
        (Nat.pow_le_pow_left (by omega : 2 ≤ m) k)
    have hx : 0 < m ^ k := pow_pos (by omega) _
    have hcross : 2 * k ≤ (m - 1) * (m ^ k - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hexp : (m ^ k - 1) + (m - 1) + 2 * k ≤ m ^ (k + 1) - 1 := by
      have hxsub : m ^ k - 1 + 1 = m ^ k := Nat.sub_add_cancel (by omega)
      have hmsub : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
      have hlast : m ^ (k + 1) - 1 + 1 = m ^ (k + 1) :=
        Nat.sub_add_cancel (by
          have hp : 0 < m ^ (k + 1) := pow_pos (by omega) _
          omega)
      rw [pow_succ] at hlast ⊢
      nlinarith
    calc
      (A ^ (k + 1) * (k + 1).factorial) ^ 3 =
          (A ^ k * k.factorial) ^ 3 * A ^ 3 * (k + 1) ^ 3 := by
        rw [pow_succ, Nat.factorial_succ]
        ring
      _ ≤ 5 ^ (m ^ k - 1) * 5 ^ (m - 1) * 5 ^ (2 * k) :=
        Nat.mul_le_mul (Nat.mul_le_mul ih hA) (factorial_step_cube_le k)
      _ = 5 ^ ((m ^ k - 1) + (m - 1) + 2 * k) := by rw [←pow_add, ←pow_add]
      _ ≤ 5 ^ (m ^ (k + 1) - 1) := Nat.pow_le_pow_right (by decide) hexp

end SymmetricSubgroupAsymptotics.ComponentOrderCubeWreathNumerics
