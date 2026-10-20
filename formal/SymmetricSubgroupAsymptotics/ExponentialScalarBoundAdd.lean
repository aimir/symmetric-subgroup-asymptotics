import SymmetricSubgroupAsymptotics.GrowingQuotientAdditiveExceptional

/-! Finite exceptional contributions may be combined before physical transfer. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ExponentialScalarBound

/-- Two proved exceptional bounds retain a positive common decay rate. -/
def add {S T : ℕ → ℝ} (E : ExponentialScalarBound S)
    (F : ExponentialScalarBound T) :
    ExponentialScalarBound (fun n => S n + T n) where
  threshold := max E.threshold F.threshold
  rate := min E.rate F.rate
  constant := E.constant + F.constant
  rate_pos := lt_min E.rate_pos F.rate_pos
  constant_pos := add_pos E.constant_pos F.constant_pos
  bound := by
    intro n hn
    have hE := E.bound n ((le_max_left _ _).trans hn)
    have hF := F.bound n ((le_max_right _ _).trans hn)
    have hEn : -E.rate * (n : ℝ) ≤ -(min E.rate F.rate) * n := by
      exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) (by positivity)
    have hFn : -F.rate * (n : ℝ) ≤ -(min E.rate F.rate) * n := by
      exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) (by positivity)
    calc
      S n + T n ≤ E.constant * (2 : ℝ)^(-E.rate * (n : ℝ)) +
          F.constant * (2 : ℝ)^(-F.rate * (n : ℝ)) := add_le_add hE hF
      _ ≤ E.constant * (2 : ℝ)^(-(min E.rate F.rate) * (n : ℝ)) +
          F.constant * (2 : ℝ)^(-(min E.rate F.rate) * (n : ℝ)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) hEn) E.constant_pos.le)
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) hFn) F.constant_pos.le)
      _ = _ := (add_mul _ _ _).symm

end SymmetricSubgroupAsymptotics.ExponentialScalarBound
