import SymmetricSubgroupAsymptotics.BinaryMixtureSmallSupportDecay

/-! A fixed polynomial number of physical parameter bins preserves
exponential negligibility, with an explicit factor-two reduction of the
decay rate. The statement is scalar and makes no counting assumption. -/
set_option autoImplicit false
open Filter

namespace SymmetricSubgroupAsymptotics.BinaryMixtureNumerics

/-- Any fixed positive prefactor and polynomial bin count can be absorbed
without altering the original pointwise rate before the summation. -/
theorem eventually_polynomial_mul_two_rpow_le (A : ℝ) (hA : 0 < A)
    (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      A*((n : ℝ)+1)^k * (2 : ℝ)^(-δ*(n : ℝ)) ≤
        (2 : ℝ)^(-(δ/2)*(n : ℝ)) := by
  obtain ⟨K, hK, hpoly⟩ := polynomial_prefactor_le_rpow_log A hA k
  filter_upwards [eventually_log_error_le_sqrt K hK
      (show 0 < δ/2 by positivity), eventually_ge_atTop 1] with n hlog hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hn0, by nlinarith [mul_nonneg (sub_nonneg.mpr hn1) hn0]⟩
  have hcost : K*Real.log ((n : ℝ)+2) ≤ (δ/2)*(n : ℝ) :=
    hlog.trans (mul_le_mul_of_nonneg_left hsqrt (by positivity))
  calc
    _ ≤ (2 : ℝ)^(K*Real.log ((n : ℝ)+2)) * (2 : ℝ)^(-δ*(n : ℝ)) :=
      mul_le_mul_of_nonneg_right (hpoly n hn) (by positivity)
    _ = (2 : ℝ)^(K*Real.log ((n : ℝ)+2)-δ*(n : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith

/-- The usual unit-prefactor form, including a fixed natural bin degree. -/
theorem eventually_polynomial_bins_le (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      ((n : ℝ)+1)^k * (2 : ℝ)^(-δ*(n : ℝ)) ≤
        (2 : ℝ)^(-(δ/2)*(n : ℝ)) := by
  simpa only [one_mul] using
    eventually_polynomial_mul_two_rpow_le 1 (by norm_num) k δ hδ

end SymmetricSubgroupAsymptotics.BinaryMixtureNumerics
