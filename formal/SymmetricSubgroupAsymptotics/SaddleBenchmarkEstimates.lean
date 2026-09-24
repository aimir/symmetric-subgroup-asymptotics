import SymmetricSubgroupAsymptotics.CoefficientIntegral
import SymmetricSubgroupAsymptotics.SaddleAssembly
import SymmetricSubgroupAsymptotics.AsymptoticTransfer

/-! The relative saddle estimate for the approved explicit benchmarks. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The common factorial and Gaussian factors cancel exactly. -/
theorem exact_div_saddleBenchmark (n : ℕ) (hn : 2 ≤ n) :
    exactBenchmark n / saddleBenchmark n =
      ((parityCoefficient n : ℝ) * saddleRadius (halfDegree n) ^ halfDegree n *
        Real.sqrt (2 * Real.pi * saddleVariance (saddleRadius (halfDegree n)))) /
      ((1 + saddleRadius (halfDegree n) / 6) ^ parity n *
        Real.exp (criticalPolynomial (saddleRadius (halfDegree n)))) := by
  have hr : 0 < halfDegree n := by dsimp [halfDegree]; omega
  have hρ := saddleRadius_pos (halfDegree n) hr
  have hb := saddleVariance_saddleRadius_pos (halfDegree n) hr
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hG : (binaryGaussianSum (halfDegree n) : ℝ) ≠ 0 := by
    exact_mod_cast (binaryGaussianSum_pos (halfDegree n)).ne'
  rw [exactBenchmark, saddleBenchmark, if_neg (not_lt.mpr hn)]
  dsimp
  field_simp

theorem exact_div_saddleBenchmark_of_coefficient_integral (n : ℕ) (hn : 2 ≤ n)
    (hcoefficient : (parityCoefficient n : ℝ) *
        saddleRadius (halfDegree n) ^ halfDegree n =
      ((1 + saddleRadius (halfDegree n) / 6) ^ parity n *
        Real.exp (criticalPolynomial (saddleRadius (halfDegree n)))) / (2 * Real.pi) *
      (∫ θ in (-Real.pi)..Real.pi,
        saddleRealKernel (saddleRadius (halfDegree n))
          (saddleParityAmplitude (saddleRadius (halfDegree n)) (parity n)) θ)) :
    exactBenchmark n / saddleBenchmark n =
      normalizedSaddleIntegral (saddleRadius (halfDegree n))
        (saddleParityAmplitude (saddleRadius (halfDegree n)) (parity n)) := by
  have hr : 0 < halfDegree n := by dsimp [halfDegree]; omega
  have hρ := saddleRadius_pos (halfDegree n) hr
  have hamp : (1 + saddleRadius (halfDegree n) / 6) ^ parity n ≠ 0 := by positivity
  have hexp := (Real.exp_pos (criticalPolynomial (saddleRadius (halfDegree n)))).ne'
  rw [exact_div_saddleBenchmark n hn, hcoefficient, normalizedSaddleIntegral]
  field_simp

/-- The exact coefficient-to-saddle ratio is the normalized real integral. -/
theorem exact_div_saddleBenchmark_eq_normalizedIntegral (n : ℕ) (hn : 2 ≤ n) :
    exactBenchmark n / saddleBenchmark n =
      normalizedSaddleIntegral (saddleRadius (halfDegree n))
        (saddleParityAmplitude (saddleRadius (halfDegree n)) (parity n)) := by
  apply exact_div_saddleBenchmark_of_coefficient_integral n hn
  have hr : 0 < halfDegree n := by dsimp [halfDegree]; omega
  have hε : parity n ≤ 1 := by dsimp [parity]; omega
  simpa only [analyticParityCoefficient_halfDegree] using
    analyticParityCoefficient_saddle_integral (parity n) (halfDegree n) hε hr

/-- The full relative saddle estimate, uniformly across both parities. -/
theorem saddleBenchmarkEstimate : SaddleBenchmarkEstimate := by
  obtain ⟨C, hC, N, hN, hbound⟩ := normalizedSaddleIntegral_rank_error
  refine ⟨3 * C, by positivity, 2 * N, by omega, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := by omega
  have hrN : N ≤ halfDegree n := by dsimp [halfDegree]; omega
  have hr : 0 < halfDegree n := by omega
  have hrpos : 0 < (halfDegree n : ℝ) := by exact_mod_cast hr
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnr : (n : ℝ) ≤ 3 * (halfDegree n : ℝ) := by
    exact_mod_cast (show n ≤ 3 * halfDegree n by dsimp [halfDegree]; omega)
  have hd := saddleParityAmplitude_mem_Icc (saddleRadius_pos (halfDegree n) hr).le (parity n)
  rw [exact_div_saddleBenchmark_eq_normalizedIntegral n hn2]
  calc
    _ ≤ C / (halfDegree n : ℝ) := hbound (halfDegree n) hrN _ hd.1 hd.2
    _ ≤ 3 * C / (n : ℝ) := by
      apply (div_le_div_iff₀ hrpos hnpos).mpr
      nlinarith [mul_le_mul_of_nonneg_left hnr hC.le]

/-- T2 requires no additional analytic hypothesis once T1 is proved. -/
theorem T2_of_T1 (hT1 : T1) : T2 :=
  T2_of_T1_and_saddleBenchmarkEstimate hT1 saddleBenchmarkEstimate

end SymmetricSubgroupAsymptotics
