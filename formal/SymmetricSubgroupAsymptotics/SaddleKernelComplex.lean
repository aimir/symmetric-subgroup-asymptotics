import SymmetricSubgroupAsymptotics.SaddleKernel

/-! The complex coefficient integrand and its real saddle kernel. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

theorem criticalComplexPolynomial_circle_re (ρ θ : ℝ) :
    (criticalComplexPolynomial (circleMap 0 ρ θ)).re =
      criticalPolynomial ρ - saddleDecay ρ θ := by
  simp [criticalComplexPolynomial, circleMap_zero_pow, circleMap_zero_re,
    criticalPolynomial, saddleDecay]
  ring

theorem criticalComplexPolynomial_circle_im (ρ θ : ℝ) :
    (criticalComplexPolynomial (circleMap 0 ρ θ)).im =
      saddlePhase ρ θ + saddleMean ρ * θ := by
  simp [criticalComplexPolynomial, circleMap_zero_pow, circleMap_zero_im,
    saddlePhase, saddleMean]
  ring

theorem saddle_centered_exponent (ρ θ : ℝ) :
    criticalComplexPolynomial (circleMap 0 ρ θ) -
      (saddleMean ρ : ℂ) * (θ : ℂ) * Complex.I =
    ((criticalPolynomial ρ - saddleDecay ρ θ : ℝ) : ℂ) +
      (saddlePhase ρ θ : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [criticalComplexPolynomial_circle_re, criticalComplexPolynomial_circle_im]

theorem saddle_centered_exponential (ρ θ : ℝ) :
    Complex.exp (criticalComplexPolynomial (circleMap 0 ρ θ)) *
      Complex.exp (-(saddleMean ρ : ℂ) * (θ : ℂ) * Complex.I) =
    ((Real.exp (criticalPolynomial ρ) * Real.exp (-saddleDecay ρ θ) : ℝ) : ℂ) *
      ((Real.cos (saddlePhase ρ θ) : ℂ) +
        (Real.sin (saddlePhase ρ θ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  have he : criticalComplexPolynomial (circleMap 0 ρ θ) +
      -(saddleMean ρ : ℂ) * (θ : ℂ) * Complex.I =
      ((criticalPolynomial ρ - saddleDecay ρ θ : ℝ) : ℂ) +
        (saddlePhase ρ θ : ℂ) * Complex.I := by
    convert saddle_centered_exponent ρ θ using 1
    ring
  rw [he, Complex.exp_add_mul_I]
  rw [← Complex.ofReal_exp, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    sub_eq_add_neg, Real.exp_add]

/-- The parity amplitude is normalized before the real part is estimated. -/
theorem saddle_integrand_re (ρ θ : ℝ) (hρ : 0 ≤ ρ) (ε : ℕ) (hε : ε ≤ 1) :
    ((1 + circleMap 0 ρ θ / 6) ^ ε *
      Complex.exp (criticalComplexPolynomial (circleMap 0 ρ θ)) *
      Complex.exp (-(saddleMean ρ : ℂ) * (θ : ℂ) * Complex.I)).re =
    (1 + ρ / 6) ^ ε * Real.exp (criticalPolynomial ρ) *
      saddleRealKernel ρ (saddleParityAmplitude ρ ε) θ := by
  rw [mul_assoc, saddle_centered_exponential]
  have hden : (6 : ℝ) + ρ ≠ 0 := by positivity
  have hcases : ε = 0 ∨ ε = 1 := by omega
  rcases hcases with rfl | rfl
  · rw [show saddleParityAmplitude ρ 0 = 0 by rfl]
    simp only [pow_zero, one_mul,
      saddleRealKernel, sub_zero, zero_mul, add_zero,
      Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_add]
    ring
  · norm_num only [pow_one, saddleParityAmplitude, Nat.one_ne_zero, if_false,
      saddleRealKernel, Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
      circleMap_zero_re, circleMap_zero_im, mul_zero, mul_one, zero_mul, zero_add,
      add_zero, sub_zero, zero_sub]
    field_simp
    ring

end SymmetricSubgroupAsymptotics
