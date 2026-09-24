import SymmetricSubgroupAsymptotics.SaddleEstimates

/-!
# The real saddle kernel

The loss and centered phase isolate the real part of the coefficient integral.
The amplitude parameter covers both parities in the interval [0,1].
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The critical polynomial evaluated at a complex argument. -/
def criticalComplexPolynomial (z : ℂ) : ℂ := z / 2 + z ^ 2 / 6 + z ^ 4 / 384

/-- The nonnegative loss in the real part of the exponent. -/
def saddleDecay (ρ θ : ℝ) : ℝ :=
  (ρ / 2) * (1 - Real.cos θ) + (ρ ^ 2 / 6) * (1 - Real.cos (2 * θ)) +
    (ρ ^ 4 / 384) * (1 - Real.cos (4 * θ))

/-- The phase after centering by the saddle mean. -/
def saddlePhase (ρ θ : ℝ) : ℝ :=
  (ρ / 2) * (Real.sin θ - θ) + (ρ ^ 2 / 6) * (Real.sin (2 * θ) - 2 * θ) +
    (ρ ^ 4 / 384) * (Real.sin (4 * θ) - 4 * θ)

/-- The normalized real coefficient kernel. -/
def saddleRealKernel (ρ d θ : ℝ) : ℝ :=
  Real.exp (-saddleDecay ρ θ) *
    ((1 - d + d * Real.cos θ) * Real.cos (saddlePhase ρ θ) -
      d * Real.sin θ * Real.sin (saddlePhase ρ θ))

/-- Zero in even degree, and the normalized linear amplitude in odd degree. -/
def saddleParityAmplitude (ρ : ℝ) (ε : ℕ) : ℝ :=
  if ε = 0 then 0 else ρ / (6 + ρ)

/-- The comparison Gaussian on the saddle circle. -/
def saddleGaussian (ρ θ : ℝ) : ℝ :=
  Real.exp (-(saddleVariance ρ) * θ ^ 2 / 2)

/-- The integral whose distance from one controls the relative saddle error. -/
def normalizedSaddleIntegral (ρ d : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi * saddleVariance ρ) / (2 * Real.pi) *
    ∫ θ in (-Real.pi)..Real.pi, saddleRealKernel ρ d θ

@[simp] theorem criticalComplexPolynomial_ofReal (x : ℝ) :
    criticalComplexPolynomial (x : ℂ) = (criticalPolynomial x : ℂ) := by
  simp [criticalComplexPolynomial, criticalPolynomial]

theorem saddleDecay_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : ℝ) : 0 ≤ saddleDecay ρ θ := by
  unfold saddleDecay
  have h1 := sub_nonneg.mpr (Real.cos_le_one θ)
  have h2 := sub_nonneg.mpr (Real.cos_le_one (2 * θ))
  have h4 := sub_nonneg.mpr (Real.cos_le_one (4 * θ))
  positivity

theorem saddleParityAmplitude_mem_Icc {ρ : ℝ} (hρ : 0 ≤ ρ) (ε : ℕ) :
    saddleParityAmplitude ρ ε ∈ Set.Icc (0 : ℝ) 1 := by
  unfold saddleParityAmplitude
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · constructor
    · positivity
    · exact (div_le_one (by positivity)).mpr (by linarith)

theorem continuous_saddleDecay (ρ : ℝ) : Continuous (saddleDecay ρ) := by
  unfold saddleDecay
  fun_prop

theorem continuous_saddlePhase (ρ : ℝ) : Continuous (saddlePhase ρ) := by
  unfold saddlePhase
  fun_prop

theorem continuous_saddleRealKernel (ρ d : ℝ) : Continuous (saddleRealKernel ρ d) := by
  unfold saddleRealKernel saddleDecay saddlePhase
  fun_prop

theorem continuous_saddleGaussian (ρ : ℝ) : Continuous (saddleGaussian ρ) := by
  unfold saddleGaussian
  fun_prop

@[simp] theorem saddleDecay_neg (ρ θ : ℝ) : saddleDecay ρ (-θ) = saddleDecay ρ θ := by
  simp [saddleDecay]

@[simp] theorem saddlePhase_neg (ρ θ : ℝ) : saddlePhase ρ (-θ) = -saddlePhase ρ θ := by
  simp [saddlePhase]
  ring

@[simp] theorem saddleRealKernel_neg (ρ d θ : ℝ) :
    saddleRealKernel ρ d (-θ) = saddleRealKernel ρ d θ := by
  simp [saddleRealKernel]

end SymmetricSubgroupAsymptotics
