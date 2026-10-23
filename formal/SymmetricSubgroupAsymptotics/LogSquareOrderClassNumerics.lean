import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! A uniform class-count budget for the logarithmic-square order
ceiling occurring in the regular/diagonal socle degree form. The finite
threshold is proved by one dyadic induction, without a numerical menu. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.LogSquareOrderClassNumerics

theorem dyadic_exponent_le (l : ℕ) (hl : 10 ≤ l) :
    3*(l+1)*(4*l+2)+2 ≤ 2*2^l := by
  induction l,hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
    calc
      3*(l+1+1)*(4*(l+1)+2)+2 ≤ 2*(3*(l+1)*(4*l+2)+2) := by nlinarith
      _ ≤ 2*(2*2^l) := Nat.mul_le_mul_left 2 ih
      _ = 2*2^(l+1) := by rw [pow_succ]; ring

theorem order_cube_le_garonziMaroti (n : ℕ) (hn : 1024 ≤ n) :
    (n^(4*Nat.log 2 n+2))^3 ≤ 5^(n-1) := by
  let l := Nat.log 2 n
  have hl : 10 ≤ l := Nat.le_log_of_pow_le (by decide : 1 < 2) (by simpa using hn)
  have hnupper : n ≤ 2^(l+1) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
  have hlower : 2^l ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hsmall := dyadic_exponent_le l hl
  have hexponent : 3*(l+1)*(4*l+2) ≤ 2*(n-1) := by omega
  calc
    (n^(4*Nat.log 2 n+2))^3 ≤ ((2^(l+1))^(4*l+2))^3 :=
      Nat.pow_le_pow_left (Nat.pow_le_pow_left hnupper _) _
    _ = 2^(3*(l+1)*(4*l+2)) := by rw [←pow_mul,←pow_mul]; congr 1; ring
    _ ≤ 2^(2*(n-1)) := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hexponent
    _ = 4^(n-1) := by rw [pow_mul]; norm_num
    _ ≤ 5^(n-1) := Nat.pow_le_pow_left (by decide : (4 : ℕ) ≤ 5) _

end SymmetricSubgroupAsymptotics.LogSquareOrderClassNumerics
