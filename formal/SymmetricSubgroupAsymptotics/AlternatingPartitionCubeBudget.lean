import SymmetricSubgroupAsymptotics.AlternatingSubnormalFibonacciBudget
import SymmetricSubgroupAsymptotics.PartitionFibonacciBound

/-! The actual partition majorant pays the GM cube budget at every
natural alternating degree at least five. The three initial values use
Fib6=8, Fib7=13 and Fib8=21, and the recurrence handles all later degrees. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.AlternatingSubnormalFibonacciBudget

theorem fib_cube_le (m : ℕ) (hm : 5 ≤ m) :
    (Nat.fib (m+1))^3 ≤ 5^(m-1) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h5 : m=5
    · subst m
      norm_num
    by_cases h6 : m=6
    · subst m
      norm_num
    by_cases h7 : m=7
    · subst m
      norm_num
    have hm8 : 8 ≤ m := by omega
    have hprev := ih (m-3) (by omega) (by omega : 5 ≤ m-3)
    have hstep : Nat.fib (m+1) ≤ 5*(Nat.fib ((m-3)+1)) := by
      have hh := fib_three_step_le (m-3)
      rw [show (m-3)+4=m+1 by omega] at hh
      exact hh
    calc
      (Nat.fib (m+1))^3 ≤ (5*(Nat.fib ((m-3)+1)))^3 :=
        Nat.pow_le_pow_left hstep 3
      _ = 5^3*(Nat.fib ((m-3)+1))^3 := mul_pow _ _ _
      _ ≤ 5^3*5^((m-3)-1) := Nat.mul_le_mul_left _ hprev
      _ = 5^(m-1) := by rw [←pow_add]; congr 1; omega

theorem partition_cube_le (m:ℕ)(hm : 5 ≤ m) :
    Nat.card (Nat.Partition m)^3≤5^(m-1) :=
  (Nat.pow_le_pow_left (PartitionFibonacciBound.partition_card_le_fib m) 3).trans (fib_cube_le m hm)

end SymmetricSubgroupAsymptotics.AlternatingSubnormalFibonacciBudget
