import SymmetricSubgroupAsymptotics.CoefficientIntegral
import SymmetricSubgroupAsymptotics.SaddleAssembly

/-!
# Quantitative shifted coefficient ratio at the same saddle

The endpoint amplitudes zero and one extract the adjacent coefficients using
the same positive radius. Uniform integral estimates therefore give the
relative error `O(1/r)` without any subgroup-counting hypothesis.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SymmetricSubgroupAsymptotics

/-- The normalized integral is affine in its amplitude parameter. -/
theorem normalizedSaddleIntegral_affine (ρ d : ℝ) :
    normalizedSaddleIntegral ρ d =
      (1-d)*normalizedSaddleIntegral ρ 0 + d*normalizedSaddleIntegral ρ 1 := by
  have hk : saddleRealKernel ρ d =
      fun θ ↦ (1-d)*saddleRealKernel ρ 0 θ + d*saddleRealKernel ρ 1 θ := by
    funext θ
    unfold saddleRealKernel
    ring
  have h0 := ((continuous_saddleRealKernel ρ 0).const_mul (1-d)).intervalIntegrable
    (μ := volume) (-Real.pi) Real.pi
  have h1 := ((continuous_saddleRealKernel ρ 1).const_mul d).intervalIntegrable
    (μ := volume) (-Real.pi) Real.pi
  unfold normalizedSaddleIntegral
  rw [hk, intervalIntegral.integral_add h0 h1]
  simp only [intervalIntegral.integral_const_mul]
  ring

private theorem analyticParityCoefficient_normalized (ε r : ℕ) (hε : ε ≤ 1)
    (hr : 0 < r) :
    (analyticParityCoefficient ε r : ℝ) * saddleRadius r ^ r *
        Real.sqrt (2*Real.pi*saddleVariance (saddleRadius r)) =
      (1+saddleRadius r/6)^ε * Real.exp (criticalPolynomial (saddleRadius r)) *
        normalizedSaddleIntegral (saddleRadius r)
          (saddleParityAmplitude (saddleRadius r) ε) := by
  rw [analyticParityCoefficient_saddle_integral ε r hε hr, normalizedSaddleIntegral]
  ring

/-- The endpoint zero extracts the unshifted coefficient. -/
theorem criticalCoefficient_normalizedSaddleIntegral_zero (r : ℕ) (hr : 0 < r) :
    normalizedSaddleIntegral (saddleRadius r) 0 =
      (criticalCoefficient r : ℝ)*saddleRadius r^r*
        Real.sqrt (2*Real.pi*saddleVariance (saddleRadius r)) /
          Real.exp (criticalPolynomial (saddleRadius r)) := by
  have h := analyticParityCoefficient_normalized 0 r (by omega) hr
  simp [analyticParityCoefficient, saddleParityAmplitude] at h
  apply (eq_div_iff (Real.exp_ne_zero _)).mpr
  linarith

/-- The endpoint one extracts `c_(r-1)` at the original radius `ρ_r`.
The positive-rank guard is needed for the literal shifted coefficient. -/
theorem criticalCoefficient_normalizedSaddleIntegral_one (r : ℕ) (hr : 0 < r) :
    normalizedSaddleIntegral (saddleRadius r) 1 =
      (criticalCoefficient (r-1) : ℝ)*saddleRadius r^r*
        Real.sqrt (2*Real.pi*saddleVariance (saddleRadius r)) /
          (saddleRadius r*Real.exp (criticalPolynomial (saddleRadius r))) := by
  let ρ := saddleRadius r
  let E := Real.exp (criticalPolynomial ρ)
  have hρ : 0 < ρ := saddleRadius_pos r hr
  have h0 := analyticParityCoefficient_normalized 0 r (by omega) hr
  have h1 := analyticParityCoefficient_normalized 1 r (by omega) hr
  simp [analyticParityCoefficient, saddleParityAmplitude] at h0
  simp [analyticParityCoefficient, saddleParityAmplitude, hr] at h1
  have hlin := normalizedSaddleIntegral_affine ρ (ρ/(6+ρ))
  have hamp : (1+ρ/6)*normalizedSaddleIntegral ρ (ρ/(6+ρ)) =
      normalizedSaddleIntegral ρ 0 + ρ/6*normalizedSaddleIntegral ρ 1 := by
    rw [hlin]
    field_simp
    ring
  change (criticalCoefficient r : ℝ)*ρ^r*Real.sqrt (2*Real.pi*saddleVariance ρ) =
    E*normalizedSaddleIntegral ρ 0 at h0
  change ((criticalCoefficient r : ℝ)+(criticalCoefficient (r-1) : ℝ)/6)*
    ρ^r*Real.sqrt (2*Real.pi*saddleVariance ρ) =
    (1+ρ/6)*E*normalizedSaddleIntegral ρ (ρ/(6+ρ)) at h1
  have hmul := congrArg (fun z : ℝ ↦ E*z) hamp
  have hshift : (criticalCoefficient (r-1) : ℝ)*ρ^r*
      Real.sqrt (2*Real.pi*saddleVariance ρ) =
      ρ*E*normalizedSaddleIntegral ρ 1 := by
    linear_combination 6*h1-6*h0+6*hmul
  change normalizedSaddleIntegral ρ 1 = _/(ρ*E)
  apply (eq_div_iff (mul_ne_zero hρ.ne' (Real.exp_ne_zero _))).mpr
  linarith

/-- Exact adjacent-coefficient ratio, with both integrals at `ρ_r`. -/
theorem criticalCoefficient_shifted_ratio_eq_integral_ratio (r : ℕ) (hr : 0 < r) :
    (criticalCoefficient (r-1) : ℝ) /
        (saddleRadius r*(criticalCoefficient r : ℝ)) =
      normalizedSaddleIntegral (saddleRadius r) 1 /
        normalizedSaddleIntegral (saddleRadius r) 0 := by
  have hρ := saddleRadius_pos r hr
  have hb := saddleVariance_saddleRadius_pos r hr
  have hc : (0:ℝ) < criticalCoefficient r := by exact_mod_cast criticalCoefficient_pos r
  have hs : 0 < Real.sqrt (2*Real.pi*saddleVariance (saddleRadius r)) := by positivity
  rw [criticalCoefficient_normalizedSaddleIntegral_one r hr,
    criticalCoefficient_normalizedSaddleIntegral_zero r hr]
  field_simp

private theorem ratio_error {a b δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/2)
    (ha : |a-1| ≤ δ) (hb : |b-1| ≤ δ) : |a/b-1| ≤ 4*δ := by
  have hb0 : 0 < b := by have := (abs_le.mp hb).1; linarith
  have hbhalf : 1/2 ≤ b := by have := (abs_le.mp hb).1; linarith
  have hab : |a-b| ≤ 2*δ := by
    calc
      |a-b| = |(a-1)-(b-1)| := by congr 1; ring
      _ ≤ |a-1|+|b-1| := abs_sub _ _
      _ ≤ 2*δ := by linarith
  calc
    |a/b-1| = |a-b|/b := by rw [← div_self hb0.ne', ← sub_div, abs_div, abs_of_pos hb0]
    _ ≤ (2*δ)/b := div_le_div_of_nonneg_right hab hb0.le
    _ ≤ 4*δ := by apply (div_le_iff₀ hb0).mpr; nlinarith

/-- An unconditional quantified form of `c_(r-1)/c_r = ρ_r (1+O(1/r))`. -/
theorem criticalCoefficient_shifted_ratio_error :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ r : ℕ, N ≤ r →
      |(criticalCoefficient (r-1) : ℝ) /
          (saddleRadius r*(criticalCoefficient r : ℝ)) - 1| ≤ C/(r:ℝ) := by
  obtain ⟨C,hC,N,hN,h⟩ := normalizedSaddleIntegral_rank_error
  obtain ⟨M,hM⟩ := exists_nat_gt (2*C)
  refine ⟨4*C,by positivity,max N M,by omega,?_⟩
  intro r hr
  have hrN : N ≤ r := le_trans (le_max_left _ _) hr
  have hr0 : 0 < r := by omega
  have hr' : (0:ℝ) < r := by exact_mod_cast hr0
  have hMr : (M:ℝ) ≤ r := by exact_mod_cast (show M ≤ r by omega)
  have hδ : C/(r:ℝ) ≤ 1/2 := (div_le_iff₀ hr').mpr (by linarith)
  rw [criticalCoefficient_shifted_ratio_eq_integral_ratio r hr0]
  have hb := ratio_error (by positivity : 0 ≤ C/(r:ℝ)) hδ
    (h r hrN 1 (by norm_num) le_rfl) (h r hrN 0 le_rfl (by norm_num))
  convert hb using 1; ring

/-- The corresponding absolute error in the unnormalized coefficient ratio. -/
theorem criticalCoefficient_shifted_ratio_absolute_error :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ r : ℕ, N ≤ r →
      |(criticalCoefficient (r-1) : ℝ)/(criticalCoefficient r : ℝ)-saddleRadius r| ≤
        C*saddleRadius r/(r:ℝ) := by
  obtain ⟨C,hC,N,hN,h⟩ := criticalCoefficient_shifted_ratio_error
  refine ⟨C,hC,N,hN,?_⟩
  intro r hr
  have hr0 : 0 < r := by omega
  have hρ := saddleRadius_pos r hr0
  have hc : (0:ℝ) < criticalCoefficient r := by exact_mod_cast criticalCoefficient_pos r
  have hid : (criticalCoefficient (r-1) : ℝ)/(criticalCoefficient r : ℝ)-saddleRadius r =
      saddleRadius r*((criticalCoefficient (r-1) : ℝ)/
        (saddleRadius r*(criticalCoefficient r : ℝ))-1) := by field_simp
  rw [hid, abs_mul, abs_of_pos hρ]
  calc
    _ ≤ saddleRadius r*(C/(r:ℝ)) := mul_le_mul_of_nonneg_left (h r hr) hρ.le
    _ = C*saddleRadius r/(r:ℝ) := by ring

/-- The exact adjacent-coefficient ratio is asymptotic to the same-rank saddle. -/
theorem criticalCoefficient_shifted_ratio_tendsto_one :
    Filter.Tendsto (fun r : ℕ ↦ (criticalCoefficient (r-1) : ℝ)/
      (saddleRadius r*(criticalCoefficient r : ℝ))) Filter.atTop (nhds 1) := by
  obtain ⟨C,hC,N,hN,h⟩ := criticalCoefficient_shifted_ratio_error
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
  · filter_upwards [Filter.eventually_ge_atTop N] with r hr
    exact h r hr
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

end SymmetricSubgroupAsymptotics
