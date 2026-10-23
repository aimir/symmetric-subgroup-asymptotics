import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! The catalogue-free affine order ceiling meets the GM cube from
sixty-four onward. Only the single endpoint64 and the dyadic logarithm
endpoint6 are separated; the entire infinite tail is uniform. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.AffineClassOrderNumerics

theorem three_succ_sq_add_two_le (l : ℕ) (hl : 7 ≤ l) :
    3*(l+1)^2+2 ≤ 2*2^l := by
  induction l,hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
    calc
      3*(l+1+1)^2+2 ≤ 2*(3*(l+1)^2+2) := by nlinarith
      _ ≤ 2*(2*2^l) := Nat.mul_le_mul_left 2 ih
      _ = 2*2^(l+1) := by rw [pow_succ]; ring

theorem domain_pow_log_cube_le (n : ℕ) (hn : 64 ≤ n) :
    (n*n^Nat.log 2 n)^3 ≤ 5^(n-1) := by
  by_cases h64 : n=64
  · subst n
    norm_num
  have hn65 : 65 ≤ n := by omega
  let l := Nat.log 2 n
  have hn0 : n ≠ 0 := by omega
  have hnupper : n ≤ 2^(l+1) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
  have hpower : 2^l ≤ n := Nat.pow_log_le_self 2 hn0
  have horder : n*n^Nat.log 2 n ≤ 2^((l+1)^2) := by
    calc
      n*n^Nat.log 2 n = n^(l+1) := by dsimp only [l]; rw [pow_succ']
      _ ≤ (2^(l+1))^(l+1) := Nat.pow_le_pow_left hnupper _
      _ = 2^((l+1)^2) := by rw [← pow_mul, pow_two]
  by_cases hl : l ≤ 6
  · have h49 : (l+1)^2 ≤ 49 := by nlinarith
    calc
      (n*n^Nat.log 2 n)^3 ≤ (2^((l+1)^2))^3 := Nat.pow_le_pow_left horder _
      _ ≤ ((2:ℕ)^49)^3 := Nat.pow_le_pow_left
        (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) h49) _
      _ ≤ 5^64 := by norm_num
      _ ≤ 5^(n-1) := Nat.pow_le_pow_right (by decide : 0 < (5:ℕ)) (by omega)
  · have hl7 : 7 ≤ l := by omega
    have hsmall := three_succ_sq_add_two_le l hl7
    have hexponent : 3*(l+1)^2 ≤ 2*(n-1) := by omega
    calc
      (n*n^Nat.log 2 n)^3 ≤ (2^((l+1)^2))^3 := Nat.pow_le_pow_left horder _
      _ = 2^(3*(l+1)^2) := by rw [← pow_mul]; congr 1; ring
      _ ≤ 2^(2*(n-1)) := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hexponent
      _ = 4^(n-1) := by rw [pow_mul]; norm_num
      _ ≤ 5^(n-1) := Nat.pow_le_pow_left (by decide : (4:ℕ) ≤ 5) _

end SymmetricSubgroupAsymptotics.AffineClassOrderNumerics
