import SymmetricSubgroupAsymptotics.TerminalGaussian

/-!
# Upper comparisons for the literal terminal Gaussian weight

The coefficient comparison is a direct inequality between the defining
finite products. The final estimate records an actual one-dimension gap,
with the summation length and both Euler factors still explicit.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- Enlarging the ambient binary space absorbs all graph choices over a
fixed quotient dimension. This is proved on the exact rational products. -/
theorem binaryGaussianCoefficient_mul_pow_le_shift (r d j : ℕ) (hj : j ≤ r) :
    binaryGaussianCoefficient r j * (2 : ℚ)^(d*j) ≤
      binaryGaussianCoefficient (r+d) j := by
  unfold binaryGaussianCoefficient
  calc
    _ = ∏ i ∈ Finset.range j,
        (((2 : ℚ)^r-2^i)/(2^j-2^i)) * 2^d := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
    _ ≤ _ := by
      apply Finset.prod_le_prod
      · intro i hi
        have hij : i < j := Finset.mem_range.mp hi
        exact mul_nonneg (div_nonneg
          (binaryGaussian_denominator_pos (hij.trans_le hj)).le
          (binaryGaussian_denominator_pos hij).le) (by positivity)
      · intro i hi
        have hij : i < j := Finset.mem_range.mp hi
        rw [div_mul_eq_mul_div]
        apply (div_le_div_iff_of_pos_right (binaryGaussian_denominator_pos hij)).mpr
        rw [pow_add]
        have hd : (1 : ℚ) ≤ 2^d := one_le_pow₀ (by norm_num)
        have hi0 : (0 : ℚ) ≤ 2^i := by positivity
        nlinarith [mul_nonneg hi0 (sub_nonneg.mpr hd)]

/-- Monotonicity retains the literal Gaussian coefficient in every term. -/
theorem terminalGaussianWeight_mono_right (r : ℕ) {d e : ℕ} (hde : d ≤ e) :
    terminalGaussianWeight r d ≤ terminalGaussianWeight r e := by
  unfold terminalGaussianWeight
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right j hde))
  exact_mod_cast (binaryGaussianCoefficient_pos (by simpa using hj)).le

/-- The terminal graph weight is bounded by the complete Gaussian sum
in the enlarged dimension, including both endpoint regimes. -/
theorem terminalGaussianWeight_le_gaussianSum (r d : ℕ) :
    terminalGaussianWeight r d ≤ (binaryGaussianSum (r+d) : ℝ) := by
  unfold terminalGaussianWeight binaryGaussianSum
  push_cast
  calc
    _ ≤ ∑ j ∈ Finset.range (r+1),
        (binaryGaussianCoefficient (r+d) j : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact_mod_cast binaryGaussianCoefficient_mul_pow_le_shift r d j
        (by simpa using hj)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega : r+1 ≤ r+d+1))
      intro j hj _
      exact_mod_cast (binaryGaussianCoefficient_pos (by simpa using hj)).le

/-- Completing the square bounds the original finite sum without replacing
its length by the larger ambient dimension. -/
theorem terminalGaussianWeight_le_quadratic (r d : ℕ) :
    terminalGaussianWeight r d ≤
      (r+1) * eulerProduct⁻¹ * (2 : ℝ)^(((r : ℝ)+d)^2/4) := by
  unfold terminalGaussianWeight
  calc
    _ ≤ ∑ _j ∈ Finset.range (r+1),
        eulerProduct⁻¹ * (2 : ℝ)^(((r : ℝ)+d)^2/4) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjr : j ≤ r := by simpa using hj
      calc
        _ ≤ (eulerProduct⁻¹ * (2 : ℝ)^(j*(r-j))) * (2 : ℝ)^(d*j) :=
          mul_le_mul_of_nonneg_right
            (binaryGaussianCoefficient_le_quadratic r j hjr) (by positivity)
        _ = eulerProduct⁻¹ * (2 : ℝ)^((j : ℝ)*((r : ℝ)-j+d)) := by
          rw [mul_assoc, ← Real.rpow_natCast (2 : ℝ) (j*(r-j)),
            ← Real.rpow_natCast (2 : ℝ) (d*j),
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 2
          push_cast [Nat.cast_sub hjr]
          ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr euler_positive.le)
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          nlinarith [sq_nonneg ((j : ℝ)-((r : ℝ)+d)/2)]
    _ = _ := by simp; ring

private theorem gaussianSum_quadratic_lower (r : ℕ) :
    eulerProduct * (2 : ℝ)^((r : ℝ)^2/4-1/4) ≤ (binaryGaussianSum r : ℝ) := by
  apply le_trans _ (quadratic_le_binaryGaussianSum r)
  apply mul_le_mul_of_nonneg_left _ euler_positive.le
  rw [← Real.rpow_natCast (2 : ℝ) (gaussianPower r), gaussianPower_quadratic]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h : (r%2 : ℕ) ≤ 1 := by omega
  have h' : ((r%2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h
  linarith

/-- A genuine one-dimension character gap gives a linear normalized loss.
The polynomial factor is exactly the original `r+1` summation length. -/
theorem terminalGaussianWeight_div_gaussian_le_rank_gap (r d C : ℕ)
    (hd : d+1 ≤ C) :
    terminalGaussianWeight r d / (binaryGaussianSum (r+C) : ℝ) ≤
      (eulerProduct⁻¹)^2 * (r+1) *
        (2 : ℝ)^(-((r : ℝ)+C)/2+1/2) := by
  have hd' : (d : ℝ)+1 ≤ C := by exact_mod_cast hd
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hupper : terminalGaussianWeight r d ≤
      (r+1) * eulerProduct⁻¹ * (2 : ℝ)^(((r : ℝ)+C-1)^2/4) := by
    apply (terminalGaussianWeight_le_quadratic r d).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity [euler_positive])
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [mul_nonneg (sub_nonneg.mpr hd')
      (show 0 ≤ 2*(r : ℝ)+C+d-1 by linarith)]
  calc
    _ ≤ ((r+1) * eulerProduct⁻¹ * (2 : ℝ)^(((r : ℝ)+C-1)^2/4)) /
        (eulerProduct * (2 : ℝ)^(((r+C : ℕ) : ℝ)^2/4-1/4)) :=
      div_le_div₀ (by positivity [euler_positive]) hupper
        (by positivity [euler_positive]) (gaussianSum_quadratic_lower (r+C))
    _ = _ := by
      push_cast
      have he : (2 : ℝ)^(((r : ℝ)+C-1)^2/4) /
          (2 : ℝ)^(((r : ℝ)+C)^2/4-1/4) =
          (2 : ℝ)^(-((r : ℝ)+C)/2+1/2) := by
        rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      calc
        _ = (eulerProduct⁻¹)^2 * ((r : ℝ)+1) *
            ((2 : ℝ)^(((r : ℝ)+C-1)^2/4) /
              (2 : ℝ)^(((r : ℝ)+C)^2/4-1/4)) := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
        _ = _ := by rw [he]

end SymmetricSubgroupAsymptotics
