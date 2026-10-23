import SymmetricSubgroupAsymptotics.ComponentOrderCubeWreathNumerics
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum

/-! A literal rank-one matrix/outer order budget pays the GM cube from
proper index64 onwards. A single dyadic induction replaces any degree
menu or finite-field enumeration. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.RankOneComponentOrderCubeNumerics

theorem dyadic_exponent_le (l : ℕ) (hl : 6 ≤ l) :
    18 + 15 * (l + 1) + 2 ≤ 2 * 2 ^ l := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
    calc
      18 + 15 * (l + 1 + 1) + 2 ≤ 2 * (18 + 15 * (l + 1) + 2) := by omega
      _ ≤ 2 * (2 * 2 ^ l) := Nat.mul_le_mul_left 2 ih
      _ = 2 * 2 ^ (l + 1) := by rw [pow_succ]; ring

theorem order_cube_le (m : ℕ) (hm : 64 ≤ m) :
    (64 * m ^ 5) ^ 3 ≤ 5 ^ (m - 1) := by
  let l := Nat.log 2 m
  have hl : 6 ≤ l := Nat.le_log_of_pow_le (by decide) (by simpa using hm)
  have hupper : m ≤ 2 ^ (l + 1) := (Nat.lt_pow_succ_log_self (by decide) m).le
  have hlower : 2 ^ l ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hd := dyadic_exponent_le l hl
  have hexp : 18 + 15 * (l + 1) ≤ 2 * (m - 1) := by omega
  calc
    (64 * m ^ 5) ^ 3 = ((2 ^ 6) * m ^ 5) ^ 3 := rfl
    _ = 2 ^ 18 * m ^ 15 := by rw [mul_pow, ←pow_mul, ←pow_mul]
    _ ≤ 2 ^ 18 * (2 ^ (l + 1)) ^ 15 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hupper 15)
    _ = 2 ^ (18 + 15 * (l + 1)) := by
      rw [←pow_mul, ←pow_add]
      congr 1
      ring
    _ ≤ 2 ^ (2 * (m - 1)) := Nat.pow_le_pow_right (by decide) hexp
    _ = (2 ^ 2) ^ (m - 1) := pow_mul _ _ _
    _ ≤ 5 ^ (m - 1) := Nat.pow_le_pow_left (by decide) _

end SymmetricSubgroupAsymptotics.RankOneComponentOrderCubeNumerics
