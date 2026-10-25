import SymmetricSubgroupAsymptotics.BinarySymmetricTopFibonacciBudget

/-! Uniform scalar reserve for the direct ternary wreath argument. The
coefficient group is allowed to be noncommutative; its order contributes six
and its three class colors contribute the cubic polynomial. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.TernarySymmetricTopFibonacciGap

def budget (n : ℕ) : ℕ := 6^n*(n+1)^3*Nat.fib (n+1)^2

theorem budget_two_step_le (n : ℕ) (hn : 28 ≤ n) :
    budget (n+2) ≤ 512*budget n := by
  have hcoeff : 324*(n+3)^3 ≤ 512*(n+1)^3 := by
    obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hn
    nlinarith [Nat.zero_le (t^3)]
  calc
    budget (n+2) = (36*6^n)*(n+3)^3*Nat.fib (n+3)^2 := by
      simp only [budget,pow_add,Nat.add_assoc]
      ring
    _ ≤ (36*6^n)*(n+3)^3*(3*Nat.fib (n+1))^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (BinarySymmetricTopFibonacciBudget.fib_two_step_le n) 2)
    _ = (324*(n+3)^3)*(6^n*Nat.fib (n+1)^2) := by ring
    _ ≤ (512*(n+1)^3)*(6^n*Nat.fib (n+1)^2) := Nat.mul_le_mul_right _ hcoeff
    _ = 512*budget n := by unfold budget; ring

theorem twice_budget_cube_gap (n : ℕ) (hn : 28 ≤ n) :
    (2*budget n)^3 ≤ 5^(6*n-4) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h28 : n=28
    · subst n; norm_num [budget]
    by_cases h29 : n=29
    · subst n; norm_num [budget]
    have hprev := ih (n-2) (by omega) (by omega : 28 ≤ n-2)
    have hstep : 2*budget n ≤ 512*(2*budget (n-2)) := by
      have hh : budget n ≤ 512*budget (n-2) := by
        simpa only [Nat.sub_add_cancel (by omega : 2 ≤ n)] using
          budget_two_step_le (n-2) (by omega)
      nlinarith
    calc
      (2*budget n)^3 ≤ (512*(2*budget (n-2)))^3 := Nat.pow_le_pow_left hstep 3
      _ = 512^3*(2*budget (n-2))^3 := mul_pow _ _ _
      _ ≤ 512^3*5^(6*(n-2)-4) := Nat.mul_le_mul_left _ hprev
      _ ≤ 5^12*5^(6*(n-2)-4) :=
        Nat.mul_le_mul_right _ (by norm_num : (512:ℕ)^3 ≤ 5^12)
      _ = 5^(6*n-4) := by rw [← pow_add]; congr 1; omega

end SymmetricSubgroupAsymptotics.TernarySymmetricTopFibonacciGap
