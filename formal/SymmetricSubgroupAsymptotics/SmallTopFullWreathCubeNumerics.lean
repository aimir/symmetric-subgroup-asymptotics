import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! The proved loose noncommutative full-wreath class bounds pay the
native two/three-block cube using only the ordinary component bound.
The deficient-kernel branch instead uses one proper-coordinate power
saving. These scalar lemmas impose no group-count hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SmallTopFullWreathCubeNumerics

private theorem cubic_step (k : ℕ) (hk : 2 ≤ k) : (k + 1) ^ 3 ≤ 5 * k ^ 3 := by
  have hlinear : 2 * (k + 1) ≤ 3 * k := by omega
  have hpower := Nat.pow_le_pow_left hlinear 3
  have hb : 2 ^ 3 * (k + 1) ^ 3 ≤ 2 ^ 3 * (5 * k ^ 3) := by
    calc
      2 ^ 3 * (k + 1) ^ 3 = (2 * (k + 1)) ^ 3 := (mul_pow _ _ _).symm
      _ ≤ (3 * k) ^ 3 := hpower
      _ = 3 ^ 3 * k ^ 3 := mul_pow _ _ _
      _ ≤ (5 * 2 ^ 3) * k ^ 3 := Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ 3 * (5 * k ^ 3) := by ring
  exact Nat.le_of_mul_le_mul_left hb (by norm_num : 0 < (2 : ℕ) ^ 3)

theorem pair_budget (a k : ℕ) (ha : 4 ≤ a) (hk : k ^ 3 ≤ 5 ^ (a - 1)) :
    (k ^ 2 + k) ^ 3 ≤ 5 ^ (2 * a - 1) := by
  by_cases hsmall : k ≤ 1
  · have h2 : k ^ 2 ≤ 1 := by simpa using Nat.pow_le_pow_left hsmall 2
    have hsum : k ^ 2 + k ≤ 2 := by omega
    exact (Nat.pow_le_pow_left hsum 3).trans
      ((by decide : 2 ^ 3 ≤ (5 : ℕ) ^ 7).trans
        (Nat.pow_le_pow_right (by decide : 0 < (5 : ℕ)) (by omega)))
  have hstep := cubic_step k (by omega)
  calc
    (k ^ 2 + k) ^ 3 = k ^ 3 * (k + 1) ^ 3 := by ring
    _ ≤ k ^ 3 * (5 * k ^ 3) := Nat.mul_le_mul_left _ hstep
    _ = 5 * (k ^ 3) ^ 2 := by ring
    _ ≤ 5 * (5 ^ (a - 1)) ^ 2 := Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left hk 2)
    _ = 5 ^ (2 * a - 1) := by
      rw [← pow_mul, ← pow_succ']
      congr 1
      omega

theorem triple_budget (a k : ℕ) (ha : 4 ≤ a) (hk : k ^ 3 ≤ 5 ^ (a - 1)) :
    (2 * (k ^ 3 + 2 * k)) ^ 3 ≤ 5 ^ (3 * a - 1) := by
  by_cases hsmall : k ≤ 2
  · have h3 : k ^ 3 ≤ 8 := by simpa using Nat.pow_le_pow_left hsmall 3
    have hsum : 2 * (k ^ 3 + 2 * k) ≤ 24 := by omega
    exact (Nat.pow_le_pow_left hsum 3).trans
      ((by decide : 24 ^ 3 ≤ (5 : ℕ) ^ 11).trans
        (Nat.pow_le_pow_right (by decide : 0 < (5 : ℕ)) (by omega)))
  have hk3 : 3 ≤ k := by omega
  have hk2 : 9 ≤ k ^ 2 := by simpa using Nat.pow_le_pow_left hk3 2
  have hlinear : 9 * (k ^ 2 + 2) ≤ 11 * k ^ 2 := by omega
  have hpower := Nat.pow_le_pow_left hlinear 3
  have hscale : 8 * (k ^ 2 + 2) ^ 3 ≤ 25 * (k ^ 2) ^ 3 := by
    have hb : 9 ^ 3 * (8 * (k ^ 2 + 2) ^ 3) ≤ 9 ^ 3 * (25 * (k ^ 2) ^ 3) := by
      calc
        9 ^ 3 * (8 * (k ^ 2 + 2) ^ 3) = 8 * (9 * (k ^ 2 + 2)) ^ 3 := by ring
        _ ≤ 8 * (11 * k ^ 2) ^ 3 := Nat.mul_le_mul_left 8 hpower
        _ = (8 * 11 ^ 3) * (k ^ 2) ^ 3 := by ring
        _ ≤ (25 * 9 ^ 3) * (k ^ 2) ^ 3 := Nat.mul_le_mul_right _ (by norm_num)
        _ = 9 ^ 3 * (25 * (k ^ 2) ^ 3) := by ring
    exact Nat.le_of_mul_le_mul_left hb (by norm_num : 0 < (9 : ℕ) ^ 3)
  calc
    (2 * (k ^ 3 + 2 * k)) ^ 3 = k ^ 3 * (8 * (k ^ 2 + 2) ^ 3) := by ring
    _ ≤ k ^ 3 * (25 * (k ^ 2) ^ 3) := Nat.mul_le_mul_left _ hscale
    _ = 25 * (k ^ 3) ^ 3 := by ring
    _ ≤ 25 * (5 ^ (a - 1)) ^ 3 := Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hk 3)
    _ = 5 ^ (3 * a - 1) := by
      rw [show (25 : ℕ) = 5 ^ 2 by decide, ← pow_mul, ← pow_add]
      congr 1
      omega

theorem proper_kernel_budget (a b t : ℕ) (ha : 4 ≤ a)
    (hb : b = 2 ∨ b = 3) (ht : t ≤ b) :
    (5 ^ (a - 2) * (5 ^ (a - 1)) ^ (b - 1)) * t ^ 3 ≤ 5 ^ (a * b - 1) := by
  have hbt : b ^ 3 ≤ 5 ^ b := by rcases hb with rfl | rfl <;> decide
  have ht' := (Nat.pow_le_pow_left ht 3).trans hbt
  calc
    (5 ^ (a - 2) * (5 ^ (a - 1)) ^ (b - 1)) * t ^ 3 ≤
        (5 ^ (a - 2) * (5 ^ (a - 1)) ^ (b - 1)) * 5 ^ b :=
      Nat.mul_le_mul_left _ ht'
    _ = 5 ^ (a * b - 1) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1
      rcases hb with rfl | rfl <;> simp only [Nat.add_sub_cancel, Nat.reduceSub, mul_one]
      all_goals omega

end SymmetricSubgroupAsymptotics.SmallTopFullWreathCubeNumerics
