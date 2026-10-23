import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Eight times the proved Fibonacci partition majorant pays the
alternating subnormal class budget. Three degree steps cost at most5,
so three explicit initial inequalities cover every m>=42. At ambient
degree>=1024 the bounded m<=41 range is absorbed uniformly as well. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.AlternatingSubnormalFibonacciBudget

theorem fib_three_step_le (n : ℕ) : Nat.fib (n+4) ≤ 5*Nat.fib (n+1) := by
  have hmono := Nat.fib_le_fib_succ (n := n)
  have h2 : Nat.fib (n+2)=Nat.fib n+Nat.fib (n+1) := Nat.fib_add_two (n := n)
  have h3 : Nat.fib (n+3)=Nat.fib (n+1)+Nat.fib (n+2) := Nat.fib_add_two (n := n+1)
  have h4 : Nat.fib (n+4)=Nat.fib (n+2)+Nat.fib (n+3) := Nat.fib_add_two (n := n+2)
  rw [h4,h3,h2]
  omega

theorem eight_fib_cube_le (m : ℕ) (hm : 42 ≤ m) :
    (8*Nat.fib (m+1))^3 ≤ 5^(m-1) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h42 : m=42
    · subst m
      norm_num
    by_cases h43 : m=43
    · subst m
      norm_num
    by_cases h44 : m=44
    · subst m
      norm_num
    have hm45 : 45 ≤ m := by omega
    have hprev := ih (m-3) (by omega) (by omega : 42 ≤ m-3)
    have hstep : 8*Nat.fib (m+1) ≤ 5*(8*Nat.fib ((m-3)+1)) := by
      have hh := Nat.mul_le_mul_left 8 (fib_three_step_le (m-3))
      rw [show (m-3)+4=m+1 by omega] at hh
      exact hh.trans_eq (by ring)
    calc
      (8*Nat.fib (m+1))^3 ≤ (5*(8*Nat.fib ((m-3)+1)))^3 :=
        Nat.pow_le_pow_left hstep 3
      _ = 5^3*(8*Nat.fib ((m-3)+1))^3 := mul_pow _ _ _
      _ ≤ 5^3*5^((m-3)-1) := Nat.mul_le_mul_left _ hprev
      _ = 5^(m-1) := by rw [←pow_add]; congr 1; omega

theorem eight_fib_cube_le_of_large_degree (m n : ℕ) (hn : 1024 ≤ n) (hmn : m ≤ n) :
    (8*Nat.fib (m+1))^3 ≤ 5^(n-1) := by
  by_cases hm : 42 ≤ m
  · exact (eight_fib_cube_le m hm).trans
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hmn 1))
  · have hm41 : m+1 ≤ 42 := by omega
    calc
      (8*Nat.fib (m+1))^3 ≤ (8*Nat.fib 42)^3 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 (Nat.fib_mono hm41)) 3
      _ ≤ 5^64 := by norm_num
      _ ≤ 5^1023 := Nat.pow_le_pow_right (by decide) (by decide)
      _ ≤ 5^(n-1) := Nat.pow_le_pow_right (by decide) (by omega)

end SymmetricSubgroupAsymptotics.AlternatingSubnormalFibonacciBudget
