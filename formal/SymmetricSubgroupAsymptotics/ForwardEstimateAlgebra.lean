import SymmetricSubgroupAsymptotics.OrdinaryFrontierClosure

/-!
# Algebra of complete exponential forward estimates

Physical producer sectors are proved independently and then assembled before
the boundedness-first recurrence is invoked.  This file packages the two
operations needed by that assembly: restriction along a proved pointwise
majorization and addition of two complete forward estimates.  Both operations
retain nonnegative forward kernels and a single exponential rate.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.OrdinaryFrontierClosure

namespace ExponentialForwardEstimate

/-- A forward estimate for a majorant applies to any eventually smaller
physical error. -/
def of_le {error majorant : ℕ → ℝ}
    (E : ExponentialForwardEstimate majorant) (N : ℕ)
    (h : ∀ n, N ≤ n → error n ≤ majorant n) :
    ExponentialForwardEstimate error where
  scalar := E.scalar
  kernel := E.kernel
  threshold := max N E.threshold
  rate := E.rate
  scalarConst := E.scalarConst
  rowConst := E.rowConst
  rate_pos := E.rate_pos
  scalarConst_pos := E.scalarConst_pos
  rowConst_nonneg := E.rowConst_nonneg
  kernel_nonneg := by
    intro n hn m hm
    exact E.kernel_nonneg n ((le_max_right N E.threshold).trans hn) m hm
  recurrence := by
    intro n hn
    exact (h n ((le_max_left N E.threshold).trans hn)).trans
      (E.recurrence n ((le_max_right N E.threshold).trans hn))
  scalar_decay := by
    intro n hn
    exact E.scalar_decay n ((le_max_right N E.threshold).trans hn)
  row_decay := by
    intro n hn
    exact E.row_decay n ((le_max_right N E.threshold).trans hn)

/-- Independent physical sectors add to one complete forward estimate.  The
new rate is the minimum of the two rates and the constants add. -/
def add {error₁ error₂ : ℕ → ℝ}
    (E₁ : ExponentialForwardEstimate error₁)
    (E₂ : ExponentialForwardEstimate error₂) :
    ExponentialForwardEstimate (fun n => error₁ n + error₂ n) where
  scalar := fun n => E₁.scalar n + E₂.scalar n
  kernel := fun n m => E₁.kernel n m + E₂.kernel n m
  threshold := max E₁.threshold E₂.threshold
  rate := min E₁.rate E₂.rate
  scalarConst := E₁.scalarConst + E₂.scalarConst
  rowConst := E₁.rowConst + E₂.rowConst
  rate_pos := lt_min E₁.rate_pos E₂.rate_pos
  scalarConst_pos := add_pos E₁.scalarConst_pos E₂.scalarConst_pos
  rowConst_nonneg := add_nonneg E₁.rowConst_nonneg E₂.rowConst_nonneg
  kernel_nonneg := by
    intro n hn m hm
    exact add_nonneg
      (E₁.kernel_nonneg n ((le_max_left E₁.threshold E₂.threshold).trans hn) m hm)
      (E₂.kernel_nonneg n ((le_max_right E₁.threshold E₂.threshold).trans hn) m hm)
  recurrence := by
    intro n hn
    have h₁ := E₁.recurrence n
      ((le_max_left E₁.threshold E₂.threshold).trans hn)
    have h₂ := E₂.recurrence n
      ((le_max_right E₁.threshold E₂.threshold).trans hn)
    calc
      error₁ n + error₂ n ≤
          (E₁.scalar n + ∑ m ∈ Finset.range n,
            E₁.kernel n m * ordinarySubgroupRatio m) +
          (E₂.scalar n + ∑ m ∈ Finset.range n,
            E₂.kernel n m * ordinarySubgroupRatio m) := add_le_add h₁ h₂
      _ = E₁.scalar n + E₂.scalar n +
          ∑ m ∈ Finset.range n,
            (E₁.kernel n m + E₂.kernel n m) * ordinarySubgroupRatio m := by
        simp only [add_mul, Finset.sum_add_distrib]
        ring
  scalar_decay := by
    intro n hn
    have h₁ := E₁.scalar_decay n
      ((le_max_left E₁.threshold E₂.threshold).trans hn)
    have h₂ := E₂.scalar_decay n
      ((le_max_right E₁.threshold E₂.threshold).trans hn)
    have hp₁ : (2 : ℝ) ^ (-E₁.rate * (n : ℝ)) ≤
        (2 : ℝ) ^ (-min E₁.rate E₂.rate * (n : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) n, min_le_left E₁.rate E₂.rate]
    have hp₂ : (2 : ℝ) ^ (-E₂.rate * (n : ℝ)) ≤
        (2 : ℝ) ^ (-min E₁.rate E₂.rate * (n : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) n, min_le_right E₁.rate E₂.rate]
    calc
      E₁.scalar n + E₂.scalar n ≤
          E₁.scalarConst * (2 : ℝ) ^ (-E₁.rate * (n : ℝ)) +
          E₂.scalarConst * (2 : ℝ) ^ (-E₂.rate * (n : ℝ)) := add_le_add h₁ h₂
      _ ≤ E₁.scalarConst * (2 : ℝ) ^ (-min E₁.rate E₂.rate * (n : ℝ)) +
          E₂.scalarConst * (2 : ℝ) ^ (-min E₁.rate E₂.rate * (n : ℝ)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hp₁ E₁.scalarConst_pos.le)
          (mul_le_mul_of_nonneg_left hp₂ E₂.scalarConst_pos.le)
      _ = (E₁.scalarConst + E₂.scalarConst) *
          (2 : ℝ) ^ (-min E₁.rate E₂.rate * (n : ℝ)) := by ring
  row_decay := by
    intro n hn
    have h₁ := E₁.row_decay n
      ((le_max_left E₁.threshold E₂.threshold).trans hn)
    have h₂ := E₂.row_decay n
      ((le_max_right E₁.threshold E₂.threshold).trans hn)
    have hp₁ : (2 : ℝ) ^ (-E₁.rate * (n : ℝ)) ≤
        (2 : ℝ) ^ (-min E₁.rate E₂.rate * (n : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) n, min_le_left E₁.rate E₂.rate]
    have hp₂ : (2 : ℝ) ^ (-E₂.rate * (n : ℝ)) ≤
        (2 : ℝ) ^ (-min E₁.rate E₂.rate * (n : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) n, min_le_right E₁.rate E₂.rate]
    calc
      (∑ m ∈ Finset.range n, (E₁.kernel n m + E₂.kernel n m)) =
          (∑ m ∈ Finset.range n, E₁.kernel n m) +
          ∑ m ∈ Finset.range n, E₂.kernel n m := by
        simp only [Finset.sum_add_distrib]
      _ ≤ E₁.rowConst * (2 : ℝ) ^ (-E₁.rate * (n : ℝ)) +
          E₂.rowConst * (2 : ℝ) ^ (-E₂.rate * (n : ℝ)) := add_le_add h₁ h₂
      _ ≤ E₁.rowConst * (2 : ℝ) ^ (-min E₁.rate E₂.rate * (n : ℝ)) +
          E₂.rowConst * (2 : ℝ) ^ (-min E₁.rate E₂.rate * (n : ℝ)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hp₁ E₁.rowConst_nonneg)
          (mul_le_mul_of_nonneg_left hp₂ E₂.rowConst_nonneg)
      _ = (E₁.rowConst + E₂.rowConst) *
          (2 : ℝ) ^ (-min E₁.rate E₂.rate * (n : ℝ)) := by ring

end ExponentialForwardEstimate

end SymmetricSubgroupAsymptotics.OrdinaryFrontierClosure

end
