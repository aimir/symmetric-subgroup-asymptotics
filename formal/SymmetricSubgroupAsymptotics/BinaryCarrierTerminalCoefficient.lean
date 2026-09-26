import SymmetricSubgroupAsymptotics.BinaryMarkedTerminalAttachment

/-! Place the original terminal coefficient in the same quadratic energy
as the carrier history. The exact Euler and 72^ell factors remain outside
that energy; no restriction comparing j and ell is introduced.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMarkedTerminalAttachment

theorem coefficient_le_energy_base (r c j ell : ℕ)
    (hell : ell ≤ c) (hc : 2*c ≤ r) :
    coefficient r c j ell ≤
      (eulerProduct⁻¹)^3 * (72 : ℝ)^ell *
        (2 : ℝ)^((ell : ℝ)*((r : ℝ)/2-ell) +
          ((j : ℝ)-ell)*((r : ℝ)-j)) := by
  have hcR : (c : ℝ) ≤ (r : ℝ)/2 := by
    have h : (2 : ℝ)*c ≤ r := by exact_mod_cast hc
    linarith
  have hp : (2 : ℝ)^(ell*(c-ell)) ≤
      (2 : ℝ)^((ell : ℝ)*((r : ℝ)/2-ell)) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast [Nat.cast_sub hell]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hcR _) (Nat.cast_nonneg ell)
  have hg : (binaryGaussianCoefficient c ell : ℝ) ≤
      eulerProduct⁻¹ * (2 : ℝ)^((ell : ℝ)*((r : ℝ)/2-ell)) :=
    (binaryGaussianCoefficient_le_quadratic c ell hell).trans
      (mul_le_mul_of_nonneg_left hp (by positivity [euler_positive]))
  unfold coefficient
  calc
    _ ≤ (eulerProduct⁻¹)^2 *
        (eulerProduct⁻¹ * (2 : ℝ)^((ell : ℝ)*((r : ℝ)/2-ell))) *
          (72 : ℝ)^ell * (2 : ℝ)^(((j : ℝ)-ell)*((r : ℝ)-j)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num) _)
      exact mul_le_mul_of_nonneg_left hg (sq_nonneg _)
    _ = _ := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring

end SymmetricSubgroupAsymptotics.BinaryMarkedTerminalAttachment
