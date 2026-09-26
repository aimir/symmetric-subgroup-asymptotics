import SymmetricSubgroupAsymptotics.ExceptionalGaussianBound
import SymmetricSubgroupAsymptotics.ElementaryParity

/-! A parity-uniform quadratic lower bound for the explicit binary Gaussian
sum. The quarter in the exponent retains the entire odd-rank loss. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

theorem binaryGaussianSum_quadratic_lower (r : ℕ) :
    eulerProduct * (2 : ℝ)^((r : ℝ)^2/4-1/4) ≤ (binaryGaussianSum r : ℝ) := by
  apply le_trans _ (quadratic_le_binaryGaussianSum r)
  apply mul_le_mul_of_nonneg_left _ euler_positive.le
  rw [← Real.rpow_natCast (2 : ℝ) (gaussianPower r), gaussianPower_quadratic]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h : (r%2 : ℕ) ≤ 1 := by omega
  have h' : ((r%2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h
  linarith

end SymmetricSubgroupAsymptotics
