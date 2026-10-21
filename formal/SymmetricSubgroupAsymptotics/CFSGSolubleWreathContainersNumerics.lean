import SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainersCount
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Conversion of the native logarithmic budget to one fixed real
polylogarithmic rate, uniformly including degree zero. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers
open CFSGSolublePrimitiveContainers

theorem logSize_add_one_real_le (b : ℕ) :
    ((logSize b + 1 : ℕ) : ℝ) ≤ 3 * Real.logb 2 ((b : ℝ) + 2) := by
  have hm : Nat.log2 b ≤ Nat.log2 (b + 2) := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right (by omega)
  have hmR : (Nat.log2 b : ℝ) ≤ Nat.log2 (b + 2) := by exact_mod_cast hm
  have hl := Real.log2_le_logb (b + 2)
  push_cast at hl
  have hlarge : 1 ≤ Real.logb 2 ((b : ℝ) + 2) := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (b : ℝ) + 2)).mpr
    simp only [Real.rpow_one]
    exact le_add_of_nonneg_left (Nat.cast_nonneg b)
  simp only [logSize, Nat.cast_add, Nat.cast_one]
  linarith

theorem logBudget_real_le (b : ℕ) :
    (logBudget b : ℝ) ≤ 81 * (Real.logb 2 ((b : ℝ) + 2)) ^ 4 := by
  have h := pow_le_pow_left₀ (by positivity :
    (0 : ℝ) ≤ ((logSize b + 1 : ℕ) : ℝ)) (logSize_add_one_real_le b) 4
  simpa only [logBudget, Nat.cast_pow, mul_pow, show (3 : ℝ) ^ 4 = 81 by norm_num] using h

theorem containerBudget_real_le (b : ℕ) :
    (containerBudget b : ℝ) ≤ 2592 * (b : ℝ) *
      (Real.logb 2 ((b : ℝ) + 2)) ^ 4 := by
  have h := mul_le_mul_of_nonneg_left (logBudget_real_le b)
    (by positivity : (0 : ℝ) ≤ 32 * (b : ℝ))
  calc
    (containerBudget b : ℝ) ≤ 32 * (b : ℝ) *
        (81 * (Real.logb 2 ((b : ℝ) + 2)) ^ 4) := by
      simpa only [containerBudget, Nat.cast_mul, Nat.cast_ofNat] using h
    _ = _ := by ring

theorem fullContainerBudget_real_le (b : ℕ) :
    ((33 * b * logBudget b : ℕ) : ℝ) ≤ 4096 * (b : ℝ) *
      (Real.logb 2 ((b : ℝ) + 2)) ^ 4 := by
  have h := mul_le_mul_of_nonneg_left (logBudget_real_le b)
    (by positivity : (0 : ℝ) ≤ 33 * (b : ℝ))
  calc
    ((33 * b * logBudget b : ℕ) : ℝ) ≤ 33 * (b : ℝ) *
        (81 * (Real.logb 2 ((b : ℝ) + 2)) ^ 4) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
    _ = 2673 * (b : ℝ) * (Real.logb 2 ((b : ℝ) + 2)) ^ 4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (2673 : ℝ) ≤ 4096)
        (Nat.cast_nonneg b)) (by positivity)

end SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers
