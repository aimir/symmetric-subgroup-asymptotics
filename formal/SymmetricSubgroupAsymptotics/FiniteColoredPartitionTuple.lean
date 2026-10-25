import SymmetricSubgroupAsymptotics.BinaryPairedPartitionFibonacciGap

/-! Coupled finite tuples of partitions. All color weights sum to the
original total, so only a polynomial factor is lost when the Fibonacci
partition bound is convolved. No partition census is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.FiniteColoredPartitionTuple

def Code : ℕ → ℕ → Type
  | 0,n => PLift (n = 0)
  | k+1,n => Σ j : Fin (n+1), Nat.Partition j.val × Code k (n-j.val)

instance finiteCode (k n : ℕ) : Finite (Code k n) := by
  induction k generalizing n with
  | zero => change Finite (PLift (n=0)); infer_instance
  | succ k ih =>
    letI : ∀ j : Fin (n+1), Fintype (Code k (n-j.val)) :=
      fun j => @Fintype.ofFinite _ (ih (n-j.val))
    letI : Fintype (Σ j : Fin (n+1), Nat.Partition j.val × Code k (n-j.val)) := inferInstance
    change Finite (Σ j : Fin (n+1), Nat.Partition j.val × Code k (n-j.val))
    infer_instance

theorem card_le_polynomial_fib (k n : ℕ) :
    Nat.card (Code k n) ≤ (n+1)^k * Nat.fib (n+1) := by
  induction k generalizing n with
  | zero =>
    have hc : Nat.card (Code 0 n) ≤ 1 := by
      change Nat.card (PLift (n=0)) ≤ 1
      exact Finite.card_le_one_iff_subsingleton.mpr inferInstance
    have hf : 1 ≤ Nat.fib (n+1) := Nat.fib_pos.mpr (by omega)
    simpa only [pow_zero,one_mul] using hc.trans hf
  | succ k ih =>
    change Nat.card (Σ j : Fin (n+1), Nat.Partition j.val × Code k (n-j.val)) ≤ _
    rw [Nat.card_sigma]
    calc
      (∑ j : Fin (n+1), Nat.card (Nat.Partition j.val × Code k (n-j.val))) =
          ∑ j : Fin (n+1), Nat.card (Nat.Partition j.val)*Nat.card (Code k (n-j.val)) := by
        simp only [Nat.card_prod]
      _ ≤ ∑ _j : Fin (n+1), (n+1)^k * Nat.fib (n+1) := by
        apply Finset.sum_le_sum
        intro j _
        have hpow : (n-j.val+1)^k ≤ (n+1)^k := Nat.pow_le_pow_left (by omega) k
        calc
          Nat.card (Nat.Partition j.val)*Nat.card (Code k (n-j.val)) ≤
              Nat.fib (j.val+1)*((n-j.val+1)^k * Nat.fib (n-j.val+1)) :=
            Nat.mul_le_mul (PartitionFibonacciBound.partition_card_le_fib j.val) (ih _)
          _ = (n-j.val+1)^k * (Nat.fib (j.val+1)*Nat.fib (n-j.val+1)) := by ring
          _ ≤ (n+1)^k * (Nat.fib (j.val+1)*Nat.fib (n-j.val+1)) :=
            Nat.mul_le_mul_right _ hpow
          _ ≤ (n+1)^k * Nat.fib (n+1) := Nat.mul_le_mul_left _
            (BinaryPairedPartitionFibonacciGap.fib_product_le n j.val
              (Nat.le_of_lt_succ j.isLt))
      _ = (n+1)^(k+1)*Nat.fib (n+1) := by simp; ring

end SymmetricSubgroupAsymptotics.FiniteColoredPartitionTuple
