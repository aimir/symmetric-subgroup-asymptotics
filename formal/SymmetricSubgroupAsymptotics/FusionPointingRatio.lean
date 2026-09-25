import SymmetricSubgroupAsymptotics.ExceptionalGaussianBound
import SymmetricSubgroupAsymptotics.AnalyticGeneratingFunction
import SymmetricSubgroupAsymptotics.FusionNumerics

/-!
# Original benchmark ratios for even-width pointing

The labelled factorial ratio is cancelled exactly against the approved
benchmark. The guarded odd coefficient is kept, including at rank zero.
No asymptotic for the unknown total subgroup count is used here.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Filter

namespace SymmetricSubgroupAsymptotics

theorem fusionGaussianSum_upper (r : ℕ) :
    (binaryGaussianSum r : ℝ) ≤
      (r+1) * eulerProduct⁻¹ * (2 : ℝ)^((r:ℝ)^2/4) := by
  unfold binaryGaussianSum
  push_cast
  calc
    _ ≤ ∑ k ∈ Finset.range (r+1), eulerProduct⁻¹ * (2:ℝ)^((r:ℝ)^2/4) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkr : k ≤ r := by simpa using hk
      apply (binaryGaussianCoefficient_le_quadratic r k hkr).trans
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr euler_positive.le)
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast [Nat.cast_sub hkr]
      nlinarith [sq_nonneg ((k:ℝ)-(r:ℝ)/2)]
    _ = _ := by simp; ring

theorem fusionGaussianSum_lower (r : ℕ) :
    eulerProduct * (2 : ℝ)^((r:ℝ)^2/4-1/4) ≤ (binaryGaussianSum r : ℝ) := by
  apply le_trans _ (quadratic_le_binaryGaussianSum r)
  apply mul_le_mul_of_nonneg_left _ euler_positive.le
  rw [← Real.rpow_natCast (2:ℝ) (gaussianPower r),gaussianPower_quadratic]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h : (r%2:ℕ) ≤ 1 := by omega
  have h' : ((r%2:ℕ):ℝ) ≤ 1 := by exact_mod_cast h
  linarith

/-- Finite backward shifts also hold for the guarded odd coefficient. -/
theorem analyticParityCoefficient_shift_le (ε k h : ℕ) :
    analyticParityCoefficient ε k ≤
      (2 * ((k+h:ℕ):ℚ))^h * analyticParityCoefficient ε (k+h) := by
  have hc := criticalCoefficient_shift_le (k+h) h (by omega)
  simp only [Nat.add_sub_cancel] at hc
  unfold analyticParityCoefficient
  by_cases he : ε = 1
  · subst ε
    by_cases hk : 0 < k
    · have hkh : 0 < k+h := by omega
      simp only [true_and, hk, hkh, if_true]
      have hs := criticalCoefficient_shift_le (k+h-1) h (by omega)
      have hi : k+h-1-h = k-1 := by omega
      rw [hi] at hs
      have hp : (2 * ((k+h-1:ℕ):ℚ))^h ≤ (2*((k+h:ℕ):ℚ))^h := by
        apply pow_le_pow_left₀ (by positivity)
        have hh : ((k+h-1:ℕ):ℚ) ≤ (k+h:ℕ) := by exact_mod_cast Nat.sub_le (k+h) 1
        linarith
      have hs' := hs.trans (mul_le_mul_of_nonneg_right hp (criticalCoefficient_nonneg _))
      nlinarith
    · have hk0 : k = 0 := by omega
      subst k
      simp only [Nat.zero_add,lt_self_iff_false,and_false,if_false,add_zero] at *
      have hp : 0 ≤ (2*(h:ℚ))^h := by positivity
      split_ifs <;> nlinarith [criticalCoefficient_nonneg (h-1)]
  · simp only [he,false_and,if_false,add_zero]
    exact hc

theorem analyticParityCoefficient_positive (ε k : ℕ) :
    0 < analyticParityCoefficient ε k := by
  unfold analyticParityCoefficient
  have hc := criticalCoefficient_pos k
  split_ifs <;> nlinarith [criticalCoefficient_nonneg (k-1)]

theorem fusionGaussianRatio_le (k h : ℕ) :
    (binaryGaussianSum k:ℝ) / binaryGaussianSum (k+h) ≤
      eulerProduct⁻¹^2 * (k+1) *
        (2:ℝ)^(-(h:ℝ)*k/2-(h:ℝ)^2/4+1/4) := by
  have hφ := euler_positive
  have hl := fusionGaussianSum_lower (k+h)
  have hu := fusionGaussianSum_upper k
  have hG : 0 < (binaryGaussianSum (k+h):ℝ) := by
    exact_mod_cast binaryGaussianSum_pos (k+h)
  calc
    _ ≤ ((k+1) * eulerProduct⁻¹ * (2:ℝ)^((k:ℝ)^2/4)) /
        (eulerProduct * (2:ℝ)^(((k+h:ℕ):ℝ)^2/4-1/4)) := by
      exact div_le_div₀ (by positivity) hu (by positivity) hl
    _ = _ := by
      push_cast
      have he : (2:ℝ)^((k:ℝ)^2/4) / (2:ℝ)^(((k:ℝ)+h)^2/4-1/4) =
          (2:ℝ)^(-(h:ℝ)*k/2-(h:ℝ)^2/4+1/4) := by
        rw [← Real.rpow_sub (by norm_num : (0:ℝ)<2)]
        congr 1
        ring
      calc
        _ = eulerProduct⁻¹^2 * ((k:ℝ)+1) *
            ((2:ℝ)^((k:ℝ)^2/4) / (2:ℝ)^(((k:ℝ)+h)^2/4-1/4)) := by
          simp only [div_eq_mul_inv,mul_inv_rev]
          ring
        _ = _ := by rw [he]

/-- Literal labelled-pointing factor with its original factorials. -/
def fusionPointingRatio (b h : ℕ) : ℝ :=
  ((b+2*h).factorial:ℝ) / (b.factorial:ℝ) * exactBenchmark b / exactBenchmark (b+2*h)

theorem fusionPointingRatio_nonneg (b h : ℕ) : 0 ≤ fusionPointingRatio b h := by
  unfold fusionPointingRatio
  have hb := exactBenchmark_pos b
  have hn := exactBenchmark_pos (b+2*h)
  positivity

/-- Factorial cancellation is exact, in both ambient parities. -/
theorem fusionPointingRatio_eq (b h : ℕ) :
    fusionPointingRatio b h =
      ((binaryGaussianSum (halfDegree b):ℝ) / binaryGaussianSum (halfDegree b+h)) *
      ((analyticParityCoefficient (parity b) (halfDegree b):ℝ) /
        analyticParityCoefficient (parity b) (halfDegree b+h)) := by
  have hr : halfDegree (b+2*h) = halfDegree b+h := by
    unfold halfDegree
    omega
  have hp : parity (b+2*h) = parity b := by
    unfold parity
    omega
  unfold fusionPointingRatio exactBenchmark
  rw [← analyticParityCoefficient_halfDegree b,
    ← analyticParityCoefficient_halfDegree (b+2*h),hr,hp]
  have hf : (b.factorial:ℝ) ≠ 0 := by positivity
  have hF : ((b+2*h).factorial:ℝ) ≠ 0 := by positivity
  field_simp

/-- A uniform explicit ratio bound, including the guarded odd coefficient.
The polynomial depends only on the removed width, and the exponential has
the full pointing loss. -/
theorem fusionPointingRatio_le (b h : ℕ) :
    fusionPointingRatio b h ≤
      (eulerProduct⁻¹^2 * (2:ℝ)^(((h:ℝ)+1)/4)) *
        (((b+2*h+1:ℕ):ℝ)^(h+1)) *
          (2:ℝ)^(-(h:ℝ)*b/4-(h:ℝ)^2/4) := by
  rw [fusionPointingRatio_eq]
  have hφ := euler_positive
  have hca : 0 < (analyticParityCoefficient (parity b) (halfDegree b):ℝ) := by
    exact_mod_cast analyticParityCoefficient_positive (parity b) (halfDegree b)
  have hcb : 0 < (analyticParityCoefficient (parity b) (halfDegree b+h):ℝ) := by
    exact_mod_cast analyticParityCoefficient_positive (parity b) (halfDegree b+h)
  have hk : 2*halfDegree b ≤ b := by unfold halfDegree; omega
  have hk' : b ≤ 2*halfDegree b+1 := by unfold halfDegree; omega
  have hcoeff : (analyticParityCoefficient (parity b) (halfDegree b):ℝ) /
      analyticParityCoefficient (parity b) (halfDegree b+h) ≤
        (2*((halfDegree b+h:ℕ):ℝ))^h := by
    have hp : 0 < (analyticParityCoefficient (parity b) (halfDegree b+h):ℝ) := by
      exact_mod_cast analyticParityCoefficient_positive (parity b) (halfDegree b+h)
    apply (div_le_iff₀ hp).mpr
    exact_mod_cast analyticParityCoefficient_shift_le (parity b) (halfDegree b) h
  have hpoly : ((halfDegree b:ℝ)+1) * (2*((halfDegree b+h:ℕ):ℝ))^h ≤
      ((b+2*h+1:ℕ):ℝ)^(h+1) := by
    rw [pow_succ']
    have ha : (halfDegree b:ℝ)+1 ≤ ((b+2*h+1:ℕ):ℝ) := by
      exact_mod_cast (show halfDegree b+1 ≤ b+2*h+1 by omega)
    have hb : 2*((halfDegree b+h:ℕ):ℝ) ≤ ((b+2*h+1:ℕ):ℝ) := by
      exact_mod_cast (show 2*(halfDegree b+h) ≤ b+2*h+1 by omega)
    exact mul_le_mul ha (pow_le_pow_left₀ (by positivity) hb h) (by positivity) (by positivity)
  have he : -(h:ℝ)*halfDegree b/2-(h:ℝ)^2/4+1/4 ≤
      ((h:ℝ)+1)/4 + (-(h:ℝ)*b/4-(h:ℝ)^2/4) := by
    have hkR : (b:ℝ) ≤ 2*(halfDegree b:ℝ)+1 := by exact_mod_cast hk'
    nlinarith [mul_nonneg (show 0 ≤ (h:ℝ) by positivity)
      (sub_nonneg.mpr hkR)]
  calc
    _ ≤ (eulerProduct⁻¹^2 * ((halfDegree b:ℝ)+1) *
        (2:ℝ)^(-(h:ℝ)*halfDegree b/2-(h:ℝ)^2/4+1/4)) *
        (2*((halfDegree b+h:ℕ):ℝ))^h := by
      exact mul_le_mul (fusionGaussianRatio_le (halfDegree b) h) hcoeff
        (by positivity) (by positivity)
    _ = eulerProduct⁻¹^2 * (((halfDegree b:ℝ)+1) *
        (2*((halfDegree b+h:ℕ):ℝ))^h) *
        (2:ℝ)^(-(h:ℝ)*halfDegree b/2-(h:ℝ)^2/4+1/4) := by ring
    _ ≤ eulerProduct⁻¹^2 * (((b+2*h+1:ℕ):ℝ)^(h+1)) *
        (2:ℝ)^(((h:ℝ)+1)/4 + (-(h:ℝ)*b/4-(h:ℝ)^2/4)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpoly (by positivity))
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) he) (by positivity) (by positivity)
    _ = _ := by rw [Real.rpow_add (by norm_num : (0:ℝ)<2)]; ring

end SymmetricSubgroupAsymptotics
