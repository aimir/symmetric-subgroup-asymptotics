import SymmetricSubgroupAsymptotics.AsymptoticTransfer

/-!
# Finite weighted counting estimates

These identities retain the original positive profile weights while combining
a common relative error with a profile-dependent exceptional contribution.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter

namespace SymmetricSubgroupAsymptotics

/-- The error in a positive weighted sum is bounded by the weighted sum of
the errors. The normalization is the complete original weight. -/
theorem finite_weighted_relative_error {ι : Type*} [Fintype ι]
    (w a ε : ι → ℝ) (G δ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i) (hG : 0 < G)
    (herror : ∀ i, |a i / G - 1| ≤ δ + ε i) :
    |(∑ i, w i * a i) / (G * ∑ i, w i) - 1| ≤
      δ + (∑ i, w i * ε i) / (∑ i, w i) := by
  have hid : (∑ i, w i * a i) / (G * ∑ i, w i) - 1 =
      (∑ i, w i * (a i / G - 1)) / (∑ i, w i) := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_one,
      ← mul_div_assoc, ← Finset.sum_div]
    field_simp [hG.ne', hW.ne']
  rw [hid, abs_div, abs_of_pos hW]
  calc
    _ ≤ (∑ i, w i * (δ + ε i)) / (∑ i, w i) := by
      apply div_le_div_of_nonneg_right _ hW.le
      calc
        _ ≤ ∑ i, |w i * (a i / G - 1)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i _
          rw [abs_mul, abs_of_nonneg (hw i)]
          exact mul_le_mul_of_nonneg_left (herror i) (hw i)
    _ = _ := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
      field_simp [hW.ne']

/-- A fixed linear prefactor can be absorbed into half of any positive
exponential decay rate, after an explicitly quantified threshold. -/
theorem eventually_rank_mul_exponential_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ r : ℕ in atTop,
      (r : ℝ) * (2 : ℝ) ^ (-c * r) ≤ (2 : ℝ) ^ (-(c / 2) * r) := by
  have hc2 : 0 < c / 2 := by positivity
  filter_upwards [eventually_exponential_le_inv_rpow hc2 1,
    eventually_ge_atTop 1] with r hr hr1
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hsmall : (r : ℝ) * (2 : ℝ) ^ (-(c / 2) * r) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hr hrpos.le
    simpa [hrpos.ne'] using this
  calc
    _ = ((r : ℝ) * (2 : ℝ) ^ (-(c / 2) * r)) *
        (2 : ℝ) ^ (-(c / 2) * r) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring
    _ ≤ 1 * (2 : ℝ) ^ (-(c / 2) * r) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = _ := one_mul _

/-- Adding two positive benchmark sectors preserves a common relative bound,
with any nonnegative original marker weight. -/
theorem relative_error_weighted_pair {a b A B w ε : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hw : 0 ≤ w)
    (ha : |a / A - 1| ≤ ε) (hb : |b / B - 1| ≤ ε) :
    |(a + w * b) / (A + w * B) - 1| ≤ ε := by
  have hden : 0 < A + w * B := add_pos_of_pos_of_nonneg hA (mul_nonneg hw hB.le)
  have ha' : |a - A| ≤ ε * A := by
    have h : a / A - 1 = (a - A) / A := by field_simp
    rw [h, abs_div, abs_of_pos hA] at ha
    exact (div_le_iff₀ hA).mp ha
  have hb' : |b - B| ≤ ε * B := by
    have h : b / B - 1 = (b - B) / B := by field_simp
    rw [h, abs_div, abs_of_pos hB] at hb
    exact (div_le_iff₀ hB).mp hb
  have hid : (a + w * b) / (A + w * B) - 1 =
      ((a - A) + w * (b - B)) / (A + w * B) := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  calc
    _ ≤ |a - A| + |w * (b - B)| := abs_add_le _ _
    _ = |a - A| + w * |b - B| := by rw [abs_mul, abs_of_nonneg hw]
    _ ≤ ε * A + w * (ε * B) := add_le_add ha' (mul_le_mul_of_nonneg_left hb' hw)
    _ = _ := by ring

end SymmetricSubgroupAsymptotics
