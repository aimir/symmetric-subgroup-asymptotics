import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! A two-step uniform estimate for the actual correlated binary
square budget. The initial degrees are twelve and thirteen, and every
two degrees multiply the budget by at most sixty-four. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinarySymmetricTopFibonacciBudget

def budget (n : ℕ) : ℕ := (n+1)*4^n*Nat.fib (n+1)

theorem fib_two_step_le (n : ℕ) : Nat.fib (n+3) ≤ 3*Nat.fib (n+1) := by
  have h := Nat.fib_le_fib_succ (n := n)
  calc
    Nat.fib (n+3) = Nat.fib (n+1) + (Nat.fib n+Nat.fib (n+1)) := by
      rw [show n+3=(n+1)+2 by omega, Nat.fib_add_two, Nat.fib_add_two]
    _ ≤ 3*Nat.fib (n+1) := by omega

theorem budget_two_step_le (n : ℕ) (hn : 5 ≤ n) : budget (n+2) ≤ 64*budget n := by
  have hcoeff : 48*(n+3) ≤ 64*(n+1) := by omega
  calc
    budget (n+2) = (n+3)*(16*4^n)*Nat.fib (n+3) := by
      simp only [budget, Nat.add_assoc, pow_add]
      ring
    _ ≤ (n+3)*(16*4^n)*(3*Nat.fib (n+1)) :=
      Nat.mul_le_mul_left _ (fib_two_step_le n)
    _ = (48*(n+3))*(4^n*Nat.fib (n+1)) := by ring
    _ ≤ (64*(n+1))*(4^n*Nat.fib (n+1)) := Nat.mul_le_mul_right _ hcoeff
    _ = 64*budget n := by unfold budget; ring

theorem budget_cube_le (n : ℕ) (hn : 12 ≤ n) :
    (budget n)^3 ≤ 5^(4*n-2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h12 : n=12
    · subst n
      norm_num [budget]
    by_cases h13 : n=13
    · subst n
      norm_num [budget]
    have hn14 : 14 ≤ n := by omega
    have hprev := ih (n-2) (by omega) (by omega : 12 ≤ n-2)
    have hstep : budget n ≤ 64*budget (n-2) := by
      have h := budget_two_step_le (n-2) (by omega)
      simpa only [Nat.sub_add_cancel (by omega : 2 ≤ n)] using h
    calc
      (budget n)^3 ≤ (64*budget (n-2))^3 := Nat.pow_le_pow_left hstep 3
      _ = 64^3*(budget (n-2))^3 := mul_pow _ _ _
      _ ≤ 64^3*5^(4*(n-2)-2) := Nat.mul_le_mul_left _ hprev
      _ ≤ 5^8*5^(4*(n-2)-2) := Nat.mul_le_mul_right _ (by norm_num : (64:ℕ)^3 ≤ 5^8)
      _ = 5^(4*n-2) := by
        rw [← pow_add]
        congr 1
        omega

end SymmetricSubgroupAsymptotics.BinarySymmetricTopFibonacciBudget
