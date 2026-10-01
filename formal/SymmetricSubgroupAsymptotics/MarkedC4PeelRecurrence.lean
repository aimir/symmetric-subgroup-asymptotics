import SymmetricSubgroupAsymptotics.MarkedC4CaseIComplete
import SymmetricSubgroupAsymptotics.MarkedC4CaseIIPeel

/-!
# Aggregating the Case-II peel recurrence

After division by `2^markedF`, Case I contributes one error factor and every
Case-II peel points to a strictly smaller physical support with the same mark
count.  Enlarging the finite peel menu to all earlier supports costs only a
factorial-size envelope.  Its logarithm is `O(b log b)`, which is within the
explicit marked-word error.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-- A positive monotone error factor closes any recurrence in which the
normalized count at `n` is bounded by that factor times one plus the sum of
all earlier normalized counts. -/
theorem normalized_peel_recurrence_le
    (x E : ℕ → ℝ)
    (hx0 : x 0 ≤ 1)
    (hE : ∀ n, 1 ≤ E n)
    (hEmono : Monotone E)
    (hrec : ∀ n, 0 < n →
      x n ≤ E n * (1 + ∑ k ∈ Finset.range n, x k)) :
    ∀ n, x n ≤ (E n * (n + 1)) ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n.eq_zero_or_pos with rfl | hn
      · simpa using hx0
      · let B : ℝ := E n * (n + 1)
        have hB : 1 ≤ B := by
          have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
            exact_mod_cast (show 1 ≤ n + 1 by omega)
          simpa only [one_mul] using
            (mul_le_mul (hE n) hn1 (by norm_num : (0 : ℝ) ≤ 1)
              (le_trans (by norm_num) (hE n)))
        have hterm : ∀ k ∈ Finset.range n, x k ≤ B ^ (n - 1) := by
          intro k hk
          have hkn : k < n := Finset.mem_range.mp hk
          have hik := ih k hkn
          have hbase : E k * (k + 1) ≤ B := by
            dsimp [B]
            exact mul_le_mul (hEmono hkn.le) (by exact_mod_cast Nat.succ_le_succ hkn.le)
              (by positivity) (le_trans (by norm_num) (hE n))
          have hbase0 : 0 ≤ E k * ((k : ℝ) + 1) :=
            mul_nonneg (le_trans (by norm_num) (hE k)) (by positivity)
          have hpow : (E k * (k + 1)) ^ k ≤ B ^ k :=
            pow_le_pow_left₀ hbase0 hbase k
          have hexp : B ^ k ≤ B ^ (n - 1) := by
            apply pow_le_pow_right₀ hB
            omega
          exact hik.trans (hpow.trans hexp)
        have hsum : (∑ k ∈ Finset.range n, x k) ≤
            (n : ℝ) * B ^ (n - 1) := by
          calc
            (∑ k ∈ Finset.range n, x k) ≤
                ∑ _k ∈ Finset.range n, B ^ (n - 1) :=
              Finset.sum_le_sum hterm
            _ = (n : ℝ) * B ^ (n - 1) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hone : (1 : ℝ) ≤ B ^ (n - 1) := one_le_pow₀ hB
        have hrecn := hrec n hn
        calc
          x n ≤ E n * (1 + ∑ k ∈ Finset.range n, x k) := hrecn
          _ ≤ E n * ((n + 1 : ℝ) * B ^ (n - 1)) := by
            apply mul_le_mul_of_nonneg_left _ (le_trans (by norm_num) (hE n))
            nlinarith
          _ = B * B ^ (n - 1) := by
            dsimp [B]
            ring
          _ = B ^ (n - 1) * B := mul_comm _ _
          _ = B ^ n := by
            rw [← pow_succ, Nat.sub_add_cancel hn]

/-- Telescoping form of a fixed Case-II peel path. -/
theorem sum_peel_cost_le
    (support cost error : ℕ → ℝ) (r : ℝ) (t : ℕ)
    (hcost : ∀ i < t,
      cost i ≤ markedF (support i) r - markedF (support (i + 1)) r + error i) :
    (∑ i ∈ Finset.range t, cost i) ≤
      markedF (support 0) r - markedF (support t) r +
        ∑ i ∈ Finset.range t, error i := by
  calc
    (∑ i ∈ Finset.range t, cost i) ≤
        ∑ i ∈ Finset.range t,
          (markedF (support i) r - markedF (support (i + 1)) r + error i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hcost i (Finset.mem_range.mp hi)
    _ = (∑ i ∈ Finset.range t,
          (markedF (support i) r - markedF (support (i + 1)) r)) +
        ∑ i ∈ Finset.range t, error i := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      have htel : ∀ q : ℕ,
          (∑ i ∈ Finset.range q,
            (markedF (support i) r - markedF (support (i + 1)) r)) =
              markedF (support 0) r - markedF (support q) r := by
        intro q
        induction q with
        | zero => simp
        | succ q ih =>
            rw [Finset.sum_range_succ, ih]
            ring
      rw [htel t]

end MarkedC4
end SymmetricSubgroupAsymptotics

end
