import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-! Pure numerical weakening of the sharp constant in Tracey's 2018
Theorem 1.1(2). This file assumes no permutation-group generator theorem.
The natural floor is retained; replacing it by a ceiling would invalidate
the small-degree argument. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TraceySharpHalfDegreeNumerics

def sharpFloor (n : ℕ) : ℕ :=
  ⌊Real.sqrt 3 * (n : ℝ) / (2 * Real.sqrt (Real.logb 2 n))⌋₊

private theorem log_lower_of_power (n a b : ℕ)
    (hpow : (2 : ℝ)^a ≤ (n : ℝ)^b) :
    (a : ℝ) ≤ b * Real.logb 2 n := by
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < 2^a) hpow
  rw [Real.logb_pow, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hl
  simpa only [mul_one] using hl

private theorem small_floor_bound (n k : ℕ) (s : ℝ) (hs : 0 < s)
    (hlog : s^2 ≤ Real.logb 2 n)
    (hbudget : (7 / 4 : ℝ) * n < (k + 1 : ℕ) * (2*s)) :
    sharpFloor n ≤ k := by
  have hroot : s ≤ Real.sqrt (Real.logb 2 n) :=
    Real.le_sqrt_of_sq_le hlog
  have hpos : 0 < Real.sqrt (Real.logb 2 n) := hs.trans_le hroot
  have hthree : Real.sqrt 3 ≤ (7 / 4 : ℝ) :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ (k + 1 : ℕ) := Nat.cast_nonneg _
  have hnum := mul_le_mul_of_nonneg_right hthree hn
  have hden := mul_le_mul_of_nonneg_left hroot hk
  have hlt : Real.sqrt 3 * (n : ℝ) /
      (2 * Real.sqrt (Real.logb 2 n)) < (k + 1 : ℕ) := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hf : sharpFloor n < k+1 :=
    (Nat.floor_lt' (Nat.succ_ne_zero k)).mpr hlt
  omega

/-- The sharp published floor pays the ordinary half-degree budget at
every degree at least four, without a parity restriction. -/
theorem sharpFloor_le_half (n : ℕ) (hn : 4 ≤ n) : sharpFloor n ≤ n/2 := by
  by_cases hlarge : 8 ≤ n
  · have hl := log_lower_of_power n 3 1 (by norm_num; exact hlarge)
    norm_num at hl
    have hs : Real.sqrt 3 ≤ Real.sqrt (Real.logb 2 n) := Real.sqrt_le_sqrt hl
    have hp : 0 < Real.sqrt (Real.logb 2 n) :=
      (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)).trans_le hs
    have hvalue : Real.sqrt 3 * (n : ℝ) /
        (2 * Real.sqrt (Real.logb 2 n)) ≤ (n : ℝ)/2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg n)
      nlinarith
    have hnonneg : 0 ≤ Real.sqrt 3 * (n : ℝ) /
        (2 * Real.sqrt (Real.logb 2 n)) := by positivity
    have hfloor := (Nat.floor_le hnonneg).trans hvalue
    have hcast : (2 * sharpFloor n : ℝ) ≤ n := by
      change 2 * (sharpFloor n : ℝ) ≤ n
      dsimp only [sharpFloor] at *
      nlinarith
    have hnat : 2 * sharpFloor n ≤ n := by exact_mod_cast hcast
    omega
  · have hcases : n=4 ∨ n=5 ∨ n=6 ∨ n=7 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · have hl := log_lower_of_power 4 2 1 (by norm_num)
      exact small_floor_bound 4 2 (7/5) (by norm_num)
        (by norm_num at hl ⊢; linarith) (by norm_num)
    · have hl := log_lower_of_power 5 9 4 (by norm_num)
      exact small_floor_bound 5 2 (3/2) (by norm_num)
        (by norm_num at hl ⊢; linarith) (by norm_num)
    · have hl := log_lower_of_power 6 2 1 (by norm_num)
      exact small_floor_bound 6 3 (7/5) (by norm_num)
        (by norm_num at hl ⊢; linarith) (by norm_num)
    · have hl := log_lower_of_power 7 8 3 (by norm_num)
      exact small_floor_bound 7 3 (8/5) (by norm_num)
        (by norm_num at hl ⊢; linarith) (by norm_num)

/-- The same result with the complete literal expression exposed. -/
theorem floor_sqrt_three_le_half (n : ℕ) (hn : 4 ≤ n) :
    ⌊Real.sqrt 3 * (n : ℝ) / (2 * Real.sqrt (Real.logb 2 n))⌋₊ ≤ n/2 :=
  sharpFloor_le_half n hn

end SymmetricSubgroupAsymptotics.TraceySharpHalfDegreeNumerics
