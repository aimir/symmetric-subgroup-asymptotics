import SymmetricSubgroupAsymptotics.Coefficients

/-!
# The critical exponential generating function

The finite rational sum in the approved benchmark is exactly the coefficient
of the formal exponential of x/2 + x²/6 + x⁴/384. This is a formal power-series
identity; analytic convergence and coefficient asymptotics are separate steps.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The critical polynomial as a rational formal power series. -/
def criticalFormalPolynomial : PowerSeries ℚ :=
  PowerSeries.C (1 / 2 : ℚ) * PowerSeries.X +
    PowerSeries.C (1 / 6 : ℚ) * PowerSeries.X ^ 2 +
    PowerSeries.C (1 / 384 : ℚ) * PowerSeries.X ^ 4

private def slope : PowerSeries ℚ :=
  PowerSeries.C (1 / 2 : ℚ) + PowerSeries.C (1 / 3 : ℚ) * PowerSeries.X ^ 1 +
    PowerSeries.C (1 / 96 : ℚ) * PowerSeries.X ^ 3

@[simp] theorem criticalFormalPolynomial_constantCoeff :
    PowerSeries.constantCoeff criticalFormalPolynomial = 0 := by
  simp [criticalFormalPolynomial]

theorem criticalFormalPolynomial_hasSubst : PowerSeries.HasSubst criticalFormalPolynomial :=
  PowerSeries.HasSubst.of_constantCoeff_zero' criticalFormalPolynomial_constantCoeff

private theorem derivative_polynomial :
    PowerSeries.derivative ℚ criticalFormalPolynomial = slope := by
  ext n
  simp only [PowerSeries.coeff_derivative, criticalFormalPolynomial, slope, map_add,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, PowerSeries.coeff_C]
  by_cases h0 : n = 0
  · subst n; norm_num
  by_cases h1 : n = 1
  · subst n; norm_num
  by_cases h3 : n = 3
  · subst n; norm_num
  have h12 : n + 1 ≠ 2 := by omega
  have h34 : n + 1 ≠ 4 := by omega
  simp [h0, h1, h3, h12, h34]

private theorem coeff_mul_slope (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (f * slope) = PowerSeries.coeff n f / 2 +
      (if 1 ≤ n then PowerSeries.coeff (n - 1) f / 3 else 0) +
      (if 3 ≤ n then PowerSeries.coeff (n - 3) f / 96 else 0) := by
  simp only [slope, mul_add, ← mul_assoc, map_add, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mul_C]
  simp [div_eq_mul_inv]

/-- Exact agreement of the finite coefficient definition with exp(P). -/
theorem criticalCoefficient_eq_exp_coeff (n : ℕ) :
    criticalCoefficient n = PowerSeries.coeff n
      ((PowerSeries.exp ℚ).subst criticalFormalPolynomial) := by
  let f : PowerSeries ℚ := (PowerSeries.exp ℚ).subst criticalFormalPolynomial
  have hzero : PowerSeries.coeff 0 f = 1 := by
    dsimp [f]
    rw [PowerSeries.coeff_subst' criticalFormalPolynomial_hasSubst]
    simp_rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
      criticalFormalPolynomial_constantCoeff]
    rw [finsum_eq_single _ 0]
    · simp
    · intro j hj
      simp [zero_pow hj]
  have hd : PowerSeries.derivative ℚ f = f * slope := by
    dsimp [f]
    rw [PowerSeries.derivative_subst ℚ criticalFormalPolynomial_hasSubst,
      PowerSeries.derivative_exp, derivative_polynomial]
  have hrec : ∀ m, ((m + 1 : ℕ) : ℚ) * PowerSeries.coeff (m + 1) f =
      PowerSeries.coeff m f / 2 +
        (if 1 ≤ m then PowerSeries.coeff (m - 1) f / 3 else 0) +
        (if 3 ≤ m then PowerSeries.coeff (m - 3) f / 96 else 0) := by
    intro m
    have hm := congrArg (PowerSeries.coeff m) hd
    rw [PowerSeries.coeff_derivative, coeff_mul_slope] at hm
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hm
  exact (congrFun (criticalCoefficient_unique (f := fun m => PowerSeries.coeff m f) hzero hrec) n).symm

/-- The whole coefficient sequence is the critical formal exponential. -/
theorem criticalSeries_eq_exp :
    PowerSeries.mk criticalCoefficient =
      (PowerSeries.exp ℚ).subst criticalFormalPolynomial := by
  ext n
  simpa using criticalCoefficient_eq_exp_coeff n

/-- The parity-adjusted benchmark coefficient is the coefficient of the
actual formal product `(1 + X/6)^ε exp(P)`, including the rank-zero cases. -/
theorem parityCoefficient_eq_exp_coeff (n : ℕ) :
    parityCoefficient n = PowerSeries.coeff (halfDegree n)
      (((1 + PowerSeries.C (1 / 6 : ℚ) * PowerSeries.X) ^ parity n) *
        (PowerSeries.exp ℚ).subst criticalFormalPolynomial) := by
  rcases parity_cases n with hp | hp
  · simp [parityCoefficient, hp, criticalCoefficient_eq_exp_coeff]
  · simp only [parityCoefficient, hp, pow_one, add_mul, one_mul, map_add,
      mul_assoc, PowerSeries.coeff_C_mul]
    have hx := PowerSeries.coeff_X_pow_mul'
      ((PowerSeries.exp ℚ).subst criticalFormalPolynomial) 1 (halfDegree n)
    simp only [pow_one] at hx
    rw [hx]
    by_cases hr : 0 < halfDegree n
    · simp [hr, show 1 ≤ halfDegree n by omega, criticalCoefficient_eq_exp_coeff,
        div_eq_mul_inv, mul_comm]
    · simp [hr, show ¬1 ≤ halfDegree n by omega, criticalCoefficient_eq_exp_coeff]

end SymmetricSubgroupAsymptotics
