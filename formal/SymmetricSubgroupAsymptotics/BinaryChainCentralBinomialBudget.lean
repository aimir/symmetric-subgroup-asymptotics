import SymmetricSubgroupAsymptotics.CentralBinomialSquareRootBound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-! A scalar budget for successive actual binary-block steps. No group
generation theorem is assumed. The finite squared Wallis estimate pays
each central coefficient by 5/6; the sum has coefficient one. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryChainCentralBinomialBudget

def middle (k : ℕ) : ℕ := k.choose (k/2)
def cumulative (k : ℕ) : ℕ := ∑ j ∈ Finset.range k, middle j

theorem cumulative_succ (k : ℕ) : cumulative (k+1) = cumulative k + middle k :=
  Finset.sum_range_succ _ _

theorem middle_mul_sqrt_le (k : ℕ) :
    (middle k : ℝ) * Real.sqrt k ≤ (5/6 : ℝ) * (2 : ℝ)^k := by
  let r : ℝ := (middle k : ℝ)/(2 : ℝ)^k
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have h := CentralBinomialSquareRootBound.normalized_square k
  change (3*(k : ℝ)+2)*r^2 ≤ 2 at h
  have hs : (Real.sqrt (k : ℝ))^2 = k := Real.sq_sqrt (Nat.cast_nonneg k)
  have hprod : (r * Real.sqrt k)^2 ≤ (5/6 : ℝ)^2 := by
    rw [mul_pow, hs]
    nlinarith [sq_nonneg r]
  have hb : r * Real.sqrt k ≤ (5/6 : ℝ) :=
    (sq_le_sq₀ (by positivity) (by norm_num)).mp hprod
  have hp : 0 < (2 : ℝ)^k := by positivity
  apply (div_le_iff₀ hp).mp
  calc
    (middle k : ℝ) * Real.sqrt k / (2 : ℝ)^k = r * Real.sqrt k := by
      dsimp [r]
      ring
    _ ≤ (5/6 : ℝ) := hb

private theorem small_square (k : ℕ) (hk : k ≤ 6) :
    cumulative k ^ 2 * k ≤ 4^k := by
  interval_cases k <;> decide +kernel

private theorem small_sqrt (k : ℕ) (hk : k ≤ 6) :
    (cumulative k : ℝ) * Real.sqrt k ≤ (2 : ℝ)^k := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
  have hp : ((2 : ℝ)^k)^2 = (4 : ℝ)^k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  rw [hp]
  exact_mod_cast small_square k hk

/-- The exact cumulative binary-chain cost has the coarse constant one,
including every finite seed. This does not assert a binary chain exists. -/
theorem cumulative_mul_sqrt_le (k : ℕ) :
    (cumulative k : ℝ) * Real.sqrt k ≤ (2 : ℝ)^k := by
  induction k with
  | zero => exact small_sqrt 0 (by omega)
  | succ k ih =>
    by_cases hk : k < 6
    · exact small_sqrt (k+1) (by omega)
    · have hkR : (6 : ℝ) ≤ k := by exact_mod_cast (by omega : 6 ≤ k)
      have hs0 := Real.sq_sqrt (Nat.cast_nonneg k)
      have hs1 := Real.sq_sqrt (Nat.cast_nonneg (k+1))
      have hscale : 11 * Real.sqrt ((k+1 : ℕ) : ℝ) ≤ 12 * Real.sqrt (k : ℝ) := by
        apply (sq_le_sq₀ (by positivity) (by positivity)).mp
        rw [mul_pow, mul_pow, hs1, hs0]
        push_cast
        nlinarith
      have hm := middle_mul_sqrt_le k
      have hsum : ((cumulative k : ℝ) + middle k) * Real.sqrt k ≤
          (11/6 : ℝ) * (2 : ℝ)^k := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hscale
        (show 0 ≤ (cumulative k : ℝ) + middle k by positivity)
      rw [cumulative_succ, Nat.cast_add, pow_succ]
      nlinarith

theorem cumulative_le_div_sqrt (k : ℕ) (hk : 1 ≤ k) :
    (cumulative k : ℝ) ≤ (2 : ℝ)^k / Real.sqrt k := by
  exact (le_div_iff₀ (Real.sqrt_pos.2
    (by exact_mod_cast (by omega : 0 < k) : (0 : ℝ) < k))).mpr
    (cumulative_mul_sqrt_le k)

end SymmetricSubgroupAsymptotics.BinaryChainCentralBinomialBudget
