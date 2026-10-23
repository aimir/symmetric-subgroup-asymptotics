import SymmetricSubgroupAsymptotics.AlternatingSubnormalFibonacciBudget

/-! The sharper alternating-or-symmetric subnormal class bound pays the
GM cube budget already from natural degree seventeen. Three exact base
inequalities and a uniform three-step recurrence cover the whole tail. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.AlternatingSubnormalFibonacciBudget

theorem two_fib_cube_le (m : ℕ) (hm : 17 ≤ m) :
    (2*Nat.fib (m+1))^3 ≤ 5^(m-1) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h17 : m=17
    · subst m
      norm_num
    by_cases h18 : m=18
    · subst m
      norm_num
    by_cases h19 : m=19
    · subst m
      norm_num
    have hm20 : 20 ≤ m := by omega
    have hprev := ih (m-3) (by omega) (by omega : 17 ≤ m-3)
    have hstep : 2*Nat.fib (m+1) ≤ 5*(2*Nat.fib ((m-3)+1)) := by
      have hh := Nat.mul_le_mul_left 2 (fib_three_step_le (m-3))
      rw [show (m-3)+4=m+1 by omega] at hh
      exact hh.trans_eq (by ring)
    calc
      (2*Nat.fib (m+1))^3 ≤ (5*(2*Nat.fib ((m-3)+1)))^3 :=
        Nat.pow_le_pow_left hstep 3
      _ = 5^3*(2*Nat.fib ((m-3)+1))^3 := mul_pow _ _ _
      _ ≤ 5^3*5^((m-3)-1) := Nat.mul_le_mul_left _ hprev
      _ = 5^(m-1) := by rw [←pow_add]; congr 1; omega

end SymmetricSubgroupAsymptotics.AlternatingSubnormalFibonacciBudget
