import SymmetricSubgroupAsymptotics.ExceptionalGaussianBound

/-! The two-column Gaussian sum for C2^r × C4^a, in the annihilator
index used by the exact lift theorem. This file proves the numerical
bound; the identification with actual subgroups is a separate theorem. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- The image dimension j and the retained annihilator dimension k are
summed independently over their full admissible ranges. -/
def cyclicFourGaussianSum (r a : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (a+1), binaryGaussianCoefficient a j *
    ∑ k ∈ Finset.range (r+a-j+1),
      binaryGaussianCoefficient (r+a-j) k * 2^(j*k)

private theorem cyclicFourGaussian_term_le (r a j k : ℕ)
    (hj : j ≤ a) (hk : k ≤ r+a-j) :
    (binaryGaussianCoefficient a j : ℝ) *
        ((binaryGaussianCoefficient (r+a-j) k : ℝ) * (2 : ℝ)^(j*k)) ≤
      (eulerProduct⁻¹)^2 * (2 : ℝ)^(((a : ℝ)^2 + ((r : ℝ)+a)^2)/4) := by
  have hjra : j ≤ r+a := by omega
  have hq := binaryGaussianCoefficient_le_quadratic a j hj
  have hq' := binaryGaussianCoefficient_le_quadratic (r+a-j) k hk
  have hq'0 : (0 : ℝ) ≤ binaryGaussianCoefficient (r+a-j) k := by
    exact_mod_cast (binaryGaussianCoefficient_pos hk).le
  have hexp : (j : ℝ)*((a : ℝ)-j) +
      (k : ℝ)*((r : ℝ)+a-k) ≤ ((a : ℝ)^2+((r : ℝ)+a)^2)/4 := by
    nlinarith [sq_nonneg ((j : ℝ)-(a : ℝ)/2),
      sq_nonneg ((k : ℝ)-((r : ℝ)+a)/2)]
  calc
    _ = (binaryGaussianCoefficient a j : ℝ) *
        (binaryGaussianCoefficient (r+a-j) k : ℝ) * (2 : ℝ)^(j*k) := by ring
    _ ≤ (eulerProduct⁻¹ * (2 : ℝ)^(j*(a-j))) *
        (eulerProduct⁻¹ * (2 : ℝ)^(k*(r+a-j-k))) * (2 : ℝ)^(j*k) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hq hq' hq'0 (by positivity [euler_positive])) (by positivity)
    _ = (eulerProduct⁻¹)^2 *
        (2 : ℝ)^((j : ℝ)*((a : ℝ)-j)+(k : ℝ)*((r : ℝ)+a-k)) := by
      have hp : (2 : ℝ)^(j*(a-j)) * (2 : ℝ)^(k*(r+a-j-k)) *
          (2 : ℝ)^(j*k) =
          (2 : ℝ)^((j : ℝ)*((a : ℝ)-j)+(k : ℝ)*((r : ℝ)+a-k)) := by
        simp only [← Real.rpow_natCast]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        push_cast [Nat.cast_sub hj,Nat.cast_sub hjra,Nat.cast_sub hk]
        ring
      calc
        _ = (eulerProduct⁻¹)^2 *
            ((2 : ℝ)^(j*(a-j)) * (2 : ℝ)^(k*(r+a-j-k)) * (2 : ℝ)^(j*k)) := by ring
        _ = _ := by rw [hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp)
      (sq_nonneg _)

/-- An explicit uniform polynomial prefactor and the two-column quadratic
exponent. No asymptotic range, parity condition or hidden count input. -/
theorem cyclicFourGaussianSum_le (r a : ℕ) :
    (cyclicFourGaussianSum r a : ℝ) ≤
      (a+1 : ℝ) * (r+a+1 : ℝ) * (eulerProduct⁻¹)^2 *
        (2 : ℝ)^(((a : ℝ)^2+((r : ℝ)+a)^2)/4) := by
  let C : ℝ := (eulerProduct⁻¹)^2 *
    (2 : ℝ)^(((a : ℝ)^2+((r : ℝ)+a)^2)/4)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  unfold cyclicFourGaussianSum
  push_cast
  simp_rw [Finset.mul_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range (a+1), ∑ _k ∈ Finset.range (r+a-j+1), C := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      exact cyclicFourGaussian_term_le r a j k
        (by simpa using hj) (by simpa using hk)
    _ ≤ ∑ _j ∈ Finset.range (a+1), (r+a+1 : ℝ) * C := by
      apply Finset.sum_le_sum
      intro j _hj
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast (show r+a-j+1 ≤ r+a+1 by omega)
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul];
                push_cast; dsimp [C]; ring

end SymmetricSubgroupAsymptotics
