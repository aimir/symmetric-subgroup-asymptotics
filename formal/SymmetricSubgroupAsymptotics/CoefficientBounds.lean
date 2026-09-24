import SymmetricSubgroupAsymptotics.Coefficients

/-!
# Analytic bounds and absolute convergence for the critical coefficient series

Dropping the degree constraint in the nonnegative finite coefficient sum gives
a product of three exponential partial sums. This proves a radius-dependent
coefficient bound, and hence absolute convergence at every complex argument.
The saddle asymptotic requires sharper estimates than this upper bound.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

private theorem exp_partial_nonneg {x : ℝ} (hx : 0 ≤ x) (r : ℕ) :
    0 ≤ ∑ a ∈ Finset.range (r + 1), x ^ a / (a.factorial : ℝ) := by
  apply Finset.sum_nonneg
  intro a ha
  positivity

/-- The positive coefficient is bounded by the exponential at any radius. -/
theorem criticalCoefficient_mul_pow_le_exp (r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (criticalCoefficient r : ℝ) * x ^ r ≤ Real.exp (criticalPolynomial x) := by
  have hsum : (criticalCoefficient r : ℝ) * x ^ r ≤
      ∑ a ∈ Finset.range (r + 1), ∑ b ∈ Finset.range (r + 1), ∑ d ∈ Finset.range (r + 1),
        ((x / 2) ^ a / (a.factorial : ℝ)) *
          ((x ^ 2 / 6) ^ b / (b.factorial : ℝ)) *
          ((x ^ 4 / 384) ^ d / (d.factorial : ℝ)) := by
    unfold criticalCoefficient
    push_cast
    simp_rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    apply Finset.sum_le_sum
    intro d hd
    split_ifs with hdegree
    · apply le_of_eq
      push_cast
      rw [← hdegree]
      simp only [pow_add, pow_mul, div_pow]
      field_simp
    · simp only [Rat.cast_zero, zero_mul]
      positivity
  calc
    _ ≤ _ := hsum
    _ = (∑ a ∈ Finset.range (r + 1), (x / 2) ^ a / (a.factorial : ℝ)) *
        (∑ b ∈ Finset.range (r + 1), (x ^ 2 / 6) ^ b / (b.factorial : ℝ)) *
        (∑ d ∈ Finset.range (r + 1), (x ^ 4 / 384) ^ d / (d.factorial : ℝ)) := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      rw [← Finset.sum_mul_sum]
    _ ≤ Real.exp (x / 2) * Real.exp (x ^ 2 / 6) * Real.exp (x ^ 4 / 384) := by
      apply mul_le_mul
      · exact mul_le_mul
          (Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ x / 2) (r + 1))
          (Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ x ^ 2 / 6) (r + 1))
          (exp_partial_nonneg (by positivity) r) (Real.exp_pos _).le
      · exact Real.sum_le_exp_of_nonneg (by positivity) (r + 1)
      · exact exp_partial_nonneg (by positivity) r
      · positivity
    _ = Real.exp (criticalPolynomial x) := by
      rw [← Real.exp_add, ← Real.exp_add]
      rfl

/-- The usual radius bound, with a strictly positive denominator. -/
theorem criticalCoefficient_le_exp_div_pow (r : ℕ) {x : ℝ} (hx : 0 < x) :
    (criticalCoefficient r : ℝ) ≤ Real.exp (criticalPolynomial x) / x ^ r :=
  (le_div_iff₀ (pow_pos hx r)).mpr (criticalCoefficient_mul_pow_le_exp r hx.le)

/-- At any fixed argument the coefficient terms admit a geometric majorant. -/
theorem criticalCoefficient_geometric_bound (r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (criticalCoefficient r : ℝ) * x ^ r ≤
      Real.exp (criticalPolynomial (2 * x)) * (1 / 2 : ℝ) ^ r := by
  have h := mul_le_mul_of_nonneg_right
    (criticalCoefficient_mul_pow_le_exp r (show 0 ≤ 2 * x by positivity))
    (show 0 ≤ (1 / 2 : ℝ) ^ r by positivity)
  have heq : (criticalCoefficient r : ℝ) * (2 * x) ^ r * (1 / 2 : ℝ) ^ r =
      (criticalCoefficient r : ℝ) * x ^ r := by
    rw [mul_assoc, ← mul_pow]
    congr 1
    ring
  rwa [heq] at h

/-- The coefficient series converges absolutely at every real argument. -/
theorem criticalCoefficient_real_summable (x : ℝ) :
    Summable (fun r : ℕ => (criticalCoefficient r : ℝ) * x ^ r) := by
  have hg : Summable (fun r : ℕ =>
      Real.exp (criticalPolynomial (2 * |x|)) * (1 / 2 : ℝ) ^ r) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul_left _
  apply hg.of_norm_bounded
  intro r
  have hc : 0 ≤ (criticalCoefficient r : ℝ) := by
    exact_mod_cast criticalCoefficient_nonneg r
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hc, Real.norm_eq_abs]
  exact criticalCoefficient_geometric_bound r (abs_nonneg x)

/-- The same majorant proves absolute convergence on the whole complex plane. -/
theorem criticalCoefficient_complex_summable (z : ℂ) :
    Summable (fun r : ℕ => (criticalCoefficient r : ℂ) * z ^ r) := by
  have hg : Summable (fun r : ℕ =>
      Real.exp (criticalPolynomial (2 * ‖z‖)) * (1 / 2 : ℝ) ^ r) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul_left _
  apply hg.of_norm_bounded
  intro r
  have hc : 0 ≤ (criticalCoefficient r : ℝ) := by
    exact_mod_cast criticalCoefficient_nonneg r
  have hnorm : ‖(criticalCoefficient r : ℂ)‖ = (criticalCoefficient r : ℝ) := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  rw [norm_mul, norm_pow, hnorm]
  exact criticalCoefficient_geometric_bound r (norm_nonneg z)

/-- Absolute summability stated explicitly for the real coefficient series. -/
theorem criticalCoefficient_real_norm_summable (x : ℝ) :
    Summable (fun r : ℕ => ‖(criticalCoefficient r : ℝ) * x ^ r‖) := by
  refine (criticalCoefficient_real_summable |x|).congr fun r => ?_
  have hc : 0 ≤ (criticalCoefficient r : ℝ) := by
    exact_mod_cast criticalCoefficient_nonneg r
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hc, Real.norm_eq_abs]

/-- Absolute summability stated explicitly on the whole complex plane. -/
theorem criticalCoefficient_complex_norm_summable (z : ℂ) :
    Summable (fun r : ℕ => ‖(criticalCoefficient r : ℂ) * z ^ r‖) := by
  refine (criticalCoefficient_real_summable ‖z‖).congr fun r => ?_
  have hc : 0 ≤ (criticalCoefficient r : ℝ) := by
    exact_mod_cast criticalCoefficient_nonneg r
  have hnorm : ‖(criticalCoefficient r : ℂ)‖ = (criticalCoefficient r : ℝ) := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  rw [norm_mul, norm_pow, hnorm]

end SymmetricSubgroupAsymptotics
