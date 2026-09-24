import SymmetricSubgroupAsymptotics.AnalyticGeneratingFunction
import SymmetricSubgroupAsymptotics.SaddleKernelComplex

/-!
# Exact coefficient extraction on a positive circle

Cauchy power-series uniqueness identifies the approved coefficient with the
circle integral. The angular form uses the symmetric interval [-π,π].
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Complex MeasureTheory

namespace SymmetricSubgroupAsymptotics

private def parityGeneratingFunction (ε : ℕ) (z : ℂ) : ℂ :=
  (1 + z / 6) ^ ε * Complex.exp (criticalComplexPolynomial z)

private theorem parityGeneratingFunction_differentiable (ε : ℕ) :
    Differentiable ℂ (parityGeneratingFunction ε) := by
  unfold parityGeneratingFunction criticalComplexPolynomial
  fun_prop

/-- Exact Cauchy formula for the approved parity coefficient at any positive radius. -/
theorem analyticParityCoefficient_cauchy (ε r : ℕ) (hε : ε ≤ 1)
    (ρ : ℝ) (hρ : 0 < ρ) :
    (analyticParityCoefficient ε r : ℂ) = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      ∮ z in C(0, ρ), z⁻¹ ^ r * z⁻¹ *
        ((1 + z / 6) ^ ε * Complex.exp (criticalComplexPolynomial z)) := by
  let radius : NNReal := ⟨ρ, hρ.le⟩
  have hRadius : (0 : NNReal) < radius := hρ
  have hC := (parityGeneratingFunction_differentiable ε).differentiableOn.hasFPowerSeriesOnBall
    (R := radius) (c := (0 : ℂ)) hRadius
  have heq := (analyticParityCoefficient_hasFPowerSeriesAt ε hε).eq_formalMultilinearSeries
    hC.hasFPowerSeriesAt
  have h := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p r (fun _ ↦ 1)) heq
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one,
    cauchyPowerSeries_apply, sub_zero, one_div, parityGeneratingFunction, mul_assoc] using h

private theorem cauchy_symmetric_angle (ε r : ℕ) (ρ : ℝ) :
    (∮ z in C(0, ρ), z⁻¹ ^ r * z⁻¹ * parityGeneratingFunction ε z) =
      ∫ θ in (-Real.pi)..Real.pi,
        (circleMap 0 ρ θ * Complex.I) *
          ((circleMap 0 ρ θ)⁻¹ ^ r * (circleMap 0 ρ θ)⁻¹ *
            parityGeneratingFunction ε (circleMap 0 ρ θ)) := by
  unfold circleIntegral
  simp only [deriv_circleMap, smul_eq_mul]
  have hp : Function.Periodic
      (fun θ ↦ (circleMap 0 ρ θ * Complex.I) *
        ((circleMap 0 ρ θ)⁻¹ ^ r * (circleMap 0 ρ θ)⁻¹ *
          parityGeneratingFunction ε (circleMap 0 ρ θ))) (2 * Real.pi) := by
    intro θ
    dsimp only
    rw [periodic_circleMap 0 ρ θ]
  have h := hp.intervalIntegral_add_eq 0 (-Real.pi)
  simpa only [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] using h

/-- Angular coefficient extraction on [-π,π], including the parity amplitude. -/
theorem analyticParityCoefficient_angular (ε r : ℕ) (hε : ε ≤ 1)
    (ρ : ℝ) (hρ : 0 < ρ) :
    (analyticParityCoefficient ε r : ℂ) * (ρ : ℂ) ^ r =
      (2 * Real.pi : ℂ)⁻¹ * ∫ θ in (-Real.pi)..Real.pi,
        (1 + circleMap 0 ρ θ / 6) ^ ε *
          Complex.exp (criticalComplexPolynomial (circleMap 0 ρ θ)) *
            Complex.exp (-(r : ℂ) * (θ : ℂ) * Complex.I) := by
  rw [analyticParityCoefficient_cauchy ε r hε ρ hρ]
  change ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
    (∮ z in C(0, ρ), z⁻¹ ^ r * z⁻¹ * parityGeneratingFunction ε z)) * (ρ : ℂ) ^ r = _
  rw [cauchy_symmetric_angle]
  rw [mul_assoc, mul_comm _ ((ρ : ℂ) ^ r), ← mul_assoc,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
  have hE : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hphase : Complex.exp (-(r : ℂ) * (θ : ℂ) * Complex.I) =
      (Complex.exp ((θ : ℂ) * Complex.I) ^ r)⁻¹ := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
    congr 1
    ring
  dsimp only
  rw [hphase]
  simp only [circleMap, zero_add, parityGeneratingFunction, mul_inv_rev, mul_pow, inv_pow]
  field_simp

/-- The exact real integral at the positive saddle, before any approximation. -/
theorem analyticParityCoefficient_saddle_integral (ε r : ℕ) (hε : ε ≤ 1)
    (hr : 0 < r) :
    (analyticParityCoefficient ε r : ℝ) * saddleRadius r ^ r =
      ((1 + saddleRadius r / 6) ^ ε * Real.exp (criticalPolynomial (saddleRadius r))) /
        (2 * Real.pi) *
          ∫ θ in (-Real.pi)..Real.pi,
            saddleRealKernel (saddleRadius r) (saddleParityAmplitude (saddleRadius r) ε) θ := by
  let ρ := saddleRadius r
  have hρ : 0 < ρ := saddleRadius_pos r hr
  have hmean : saddleMean ρ = (r : ℝ) := saddleMean_saddleRadius r hr
  let f : ℝ → ℂ := fun θ ↦ (1 + circleMap 0 ρ θ / 6) ^ ε *
    Complex.exp (criticalComplexPolynomial (circleMap 0 ρ θ)) *
      Complex.exp (-(r : ℂ) * (θ : ℂ) * Complex.I)
  have hf : Continuous f := by
    dsimp [f]
    unfold criticalComplexPolynomial
    fun_prop
  have hi : IntervalIntegrable f volume (-Real.pi) Real.pi := hf.intervalIntegrable _ _
  have hc := analyticParityCoefficient_angular ε r hε ρ hρ
  change (analyticParityCoefficient ε r : ℂ) * (ρ : ℂ) ^ r =
    (2 * Real.pi : ℂ)⁻¹ * ∫ θ in (-Real.pi)..Real.pi, f θ at hc
  have hcre : (analyticParityCoefficient ε r : ℝ) * ρ ^ r =
      (2 * Real.pi)⁻¹ * (∫ θ in (-Real.pi)..Real.pi, f θ).re := by
    have h := congrArg Complex.re hc
    simpa only [← Complex.ofReal_ratCast, ← Complex.ofReal_pow, ← Complex.ofReal_ofNat,
      ← Complex.ofReal_mul, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using h
  have hre : ∀ θ : ℝ, (f θ).re =
      ((1 + ρ / 6) ^ ε * Real.exp (criticalPolynomial ρ)) *
        saddleRealKernel ρ (saddleParityAmplitude ρ ε) θ := by
    intro θ
    have h := saddle_integrand_re ρ θ hρ.le ε hε
    rw [hmean] at h
    simpa only [Complex.ofReal_natCast, f] using h
  have hri : (∫ θ in (-Real.pi)..Real.pi, f θ).re =
      ∫ θ in (-Real.pi)..Real.pi, (f θ).re := by
    exact (Complex.reCLM.intervalIntegral_comp_comm hi).symm
  rw [hri] at hcre
  simp_rw [hre] at hcre
  rw [intervalIntegral.integral_const_mul] at hcre
  dsimp [ρ] at hcre
  rw [hcre]
  ring

end SymmetricSubgroupAsymptotics
