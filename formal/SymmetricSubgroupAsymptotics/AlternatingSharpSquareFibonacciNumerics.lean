import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.IntervalCases

/-! A selected five-base integer pilot for two alternating factors.
The envelope uses only the proved Fibonacci partition majorant. The
actual degree is allowed to be ANY b>=m^2, not just the minimum. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.AlternatingSharpSquareFibonacciNumerics

def envelope (m : ℕ) : ℕ := (4*Nat.fib (m+1))^2*2

theorem binary_product_cube_gap (m b : ℕ) (hm : 5 ≤ m) (hm9 : m ≤ 9)
    (hdegree : m^2 ≤ b) :
    (2^b*envelope m)^3 ≤ 5^(2*b-2) := by
  induction b,hdegree using Nat.le_induction with
  | base =>
    interval_cases m <;> norm_num [envelope]
  | succ b hb ih =>
    have hmsq : 25 ≤ m^2 := by simpa only [pow_two] using Nat.mul_le_mul hm hm
    have hb2 : 2 ≤ b := by omega
    calc
      (2^(b+1)*envelope m)^3 = 8*(2^b*envelope m)^3 := by rw [pow_succ]; ring
      _ ≤ 8*5^(2*b-2) := Nat.mul_le_mul_left _ ih
      _ ≤ 25*5^(2*b-2) := Nat.mul_le_mul_right _ (by decide : (8:ℕ) ≤ 25)
      _ = 5^(2*(b+1)-2) := by
        rw [show 2*(b+1)-2=(2*b-2)+2 by omega,pow_add]
        ring

end SymmetricSubgroupAsymptotics.AlternatingSharpSquareFibonacciNumerics
