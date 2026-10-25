import SymmetricSubgroupAsymptotics.BinaryPartitionBudget
import SymmetricSubgroupAsymptotics.PartitionFibonacciBound
import SymmetricSubgroupAsymptotics.BinarySymmetricTopFibonacciBudget

/-! A sharper binary colored-partition budget. The convolution of the
partition Fibonacci bounds uses the Fibonacci addition identity rather
than replacing each summand by a binary power. The resulting square
budget has a full class-cube exponent reserve, including a factor two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairedPartitionFibonacciGap
open BinaryPartitionBudget

theorem fib_product_le (n k : ℕ) (hk : k ≤ n) :
    Nat.fib (k+1) * Nat.fib (n-k+1) ≤ Nat.fib (n+1) := by
  have h := Nat.fib_add k (n-k)
  rw [Nat.add_sub_of_le hk] at h
  omega

theorem pairedPartitions_card_le_fib (n : ℕ) :
    Nat.card (PairedPartitions n) ≤ (n+1)*Nat.fib (n+1) := by
  rw [Nat.card_sigma]
  calc
    (∑ i : Fin (n+1), Nat.card (Nat.Partition i.val × Nat.Partition (n-i.val))) =
        ∑ i : Fin (n+1), Nat.card (Nat.Partition i.val)*Nat.card (Nat.Partition (n-i.val)) := by
      simp only [Nat.card_prod]
    _ ≤ ∑ _i : Fin (n+1), Nat.fib (n+1) := by
      apply Finset.sum_le_sum
      intro i _
      exact (Nat.mul_le_mul (PartitionFibonacciBound.partition_card_le_fib i.val)
        (PartitionFibonacciBound.partition_card_le_fib (n-i.val))).trans
          (fib_product_le n i.val (Nat.le_of_lt_succ i.isLt))
    _ = (n+1)*Nat.fib (n+1) := by simp

def budget (n : ℕ) : ℕ := (n+1)*2^n*Nat.fib (n+1)^2

theorem budget_two_step_le (n : ℕ) (hn : 2 ≤ n) : budget (n+2) ≤ 64*budget n := by
  have hcoeff : 36*(n+3) ≤ 64*(n+1) := by omega
  calc
    budget (n+2) = (n+3)*(4*2^n)*Nat.fib (n+3)^2 := by
      simp only [budget, Nat.add_assoc, pow_add]
      ring
    _ ≤ (n+3)*(4*2^n)*(3*Nat.fib (n+1))^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (BinarySymmetricTopFibonacciBudget.fib_two_step_le n) 2)
    _ = (36*(n+3))*(2^n*Nat.fib (n+1)^2) := by ring
    _ ≤ (64*(n+1))*(2^n*Nat.fib (n+1)^2) := Nat.mul_le_mul_right _ hcoeff
    _ = 64*budget n := by unfold budget; ring

theorem budget_cube_gap (n : ℕ) (hn : 8 ≤ n) :
    (budget n)^3 ≤ 5^(4*n-4) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h8 : n=8
    · subst n; norm_num [budget]
    by_cases h9 : n=9
    · subst n; norm_num [budget]
    have hprev := ih (n-2) (by omega) (by omega : 8 ≤ n-2)
    have hstep : budget n ≤ 64*budget (n-2) := by
      simpa only [Nat.sub_add_cancel (by omega : 2 ≤ n)] using
        (budget_two_step_le (n-2) (by omega))
    calc
      (budget n)^3 ≤ (64*budget (n-2))^3 := Nat.pow_le_pow_left hstep 3
      _ = 64^3*(budget (n-2))^3 := mul_pow _ _ _
      _ ≤ 64^3*5^(4*(n-2)-4) := Nat.mul_le_mul_left _ hprev
      _ ≤ 5^8*5^(4*(n-2)-4) := Nat.mul_le_mul_right _ (by norm_num : (64:ℕ)^3 ≤ 5^8)
      _ = 5^(4*n-4) := by rw [← pow_add]; congr 1; omega

theorem twice_budget_cube_gap (n : ℕ) (hn : 10 ≤ n) :
    (2*budget n)^3 ≤ 5^(4*n-4) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h10 : n=10
    · subst n; norm_num [budget]
    by_cases h11 : n=11
    · subst n; norm_num [budget]
    have hprev := ih (n-2) (by omega) (by omega : 10 ≤ n-2)
    have hstep : 2*budget n ≤ 64*(2*budget (n-2)) := by
      have h := budget_two_step_le (n-2) (by omega)
      have hh : budget n ≤ 64*budget (n-2) := by
        simpa only [Nat.sub_add_cancel (by omega : 2 ≤ n)] using h
      nlinarith
    calc
      (2*budget n)^3 ≤ (64*(2*budget (n-2)))^3 := Nat.pow_le_pow_left hstep 3
      _ = 64^3*(2*budget (n-2))^3 := mul_pow _ _ _
      _ ≤ 64^3*5^(4*(n-2)-4) := Nat.mul_le_mul_left _ hprev
      _ ≤ 5^8*5^(4*(n-2)-4) := Nat.mul_le_mul_right _ (by norm_num : (64:ℕ)^3 ≤ 5^8)
      _ = 5^(4*n-4) := by rw [← pow_add]; congr 1; omega

end SymmetricSubgroupAsymptotics.BinaryPairedPartitionFibonacciGap
