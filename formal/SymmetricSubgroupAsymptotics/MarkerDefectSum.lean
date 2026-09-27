import SymmetricSubgroupAsymptotics.BinaryMixturePolynomialDecay
import SymmetricSubgroupAsymptotics.MarkerQuadraticDeficit
import Mathlib.Order.Interval.Finset.Nat

/-!
# Summing the quantitative marker defect envelope

The eventual threshold is uniform in the positive defect. This is a
numerical theorem: applying it to a physical counting kernel still requires
proving that kernel's stated pointwise envelope with one constant C.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.MarkerDefectSum

open BinaryMixtureNumerics

theorem eventually_log_error_le_linear (C : ℝ) (hC : 0 ≤ C)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      C * Real.log ((N : ℝ) + 2) ≤ epsilon * N := by
  filter_upwards [eventually_log_error_le_sqrt C hC hepsilon,
    eventually_ge_atTop 1] with N hlog hN
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrt : Real.sqrt (N : ℝ) ≤ N := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hN0, by nlinarith [mul_nonneg (sub_nonneg.mpr hN1) hN0]⟩
  exact hlog.trans (mul_le_mul_of_nonneg_left hsqrt hepsilon.le)

/-- A single eventual threshold works for every positive defect. -/
theorem eventually_uniform_defect_bound (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℕ, 1 ≤ D →
      (2 : ℝ) ^ (-13 * N * D / 60 + C * D * Real.log ((N : ℝ) + 2)) ≤
        (2 : ℝ) ^ (-(N : ℝ) / 5) := by
  filter_upwards [eventually_log_error_le_linear C hC
    (by norm_num : (0 : ℝ) < 1 / 60)] with N hlog
  intro D hD
  have hD0 : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hD1 : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hcost := mul_le_mul_of_nonneg_right hlog hD0
  have hND := mul_le_mul_of_nonneg_left hD1 hN0
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith

/-- A proved pointwise logarithmic envelope yields the complete finite
row estimate, without a separate geometric-series argument. -/
theorem eventually_defect_sum_le (C : ℝ) (hC : 0 ≤ C)
    (W : ℕ → ℕ → ℝ)
    (hW : ∀ᶠ N : ℕ in atTop, ∀ D ∈ Finset.Icc 1 N,
      W N D ≤ (2 : ℝ) ^
        (-13 * N * D / 60 + C * D * Real.log ((N : ℝ) + 2))) :
    ∀ᶠ N : ℕ in atTop,
      (∑ D ∈ Finset.Icc 1 N, W N D) ≤ (2 : ℝ) ^ (-(N : ℝ) / 10) := by
  filter_upwards [hW, eventually_uniform_defect_bound C hC,
    eventually_polynomial_bins_le 1 (1 / 5) (by norm_num)] with N hW hdefect hpoly
  calc
    _ ≤ ∑ _D ∈ Finset.Icc 1 N, (2 : ℝ) ^ (-(N : ℝ) / 5) := by
      apply Finset.sum_le_sum
      intro D hD
      exact (hW D hD).trans (hdefect D (Finset.mem_Icc.mp hD).1)
    _ = (N : ℝ) * (2 : ℝ) ^ (-(N : ℝ) / 5) := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
        nsmul_eq_mul]
    _ ≤ ((N : ℝ) + 1) ^ 1 * (2 : ℝ) ^ (-(N : ℝ) / 5) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simp
    _ ≤ _ := by
      convert hpoly using 1 <;> congr 1 <;> ring

end SymmetricSubgroupAsymptotics.MarkerDefectSum

end
