import SymmetricSubgroupAsymptotics.ElementaryTransfer
import SymmetricSubgroupAsymptotics.ElementaryParity
import SymmetricSubgroupAsymptotics.ElementarySaddle
import SymmetricSubgroupAsymptotics.SaddleBenchmarkEstimates
import SymmetricSubgroupAsymptotics.DefinitionsVerified

/-!
# The elementary benchmark estimate and the implication T1 → T3

The logarithmic factorial, Gaussian and saddle estimates first give the
rank-based model.  The exact residue normalization and the parity-shift
bound identify its degree-based form.  Exponentiation and the already
proved saddle estimate then give the approved first correction.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- All analytic factors of the saddle benchmark have a uniform logarithmic
remainder on the degree square-root scale. -/
theorem log_saddleBenchmark_model_error :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      |Real.log (saddleBenchmark n) - elementaryLogModel n| ≤
        1000263 / Real.sqrt (n : ℝ) := by
  obtain ⟨NG, hNG, hG⟩ := binaryGaussianSum_log_error
  refine ⟨2 * max NG 683, by omega, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hrG : NG ≤ halfDegree n := by dsimp [halfDegree]; omega
  have hr683 : 683 ≤ halfDegree n := by dsimp [halfDegree]; omega
  have hr0 : 0 < halfDegree n := by omega
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hr' : 0 < (halfDegree n : ℝ) := by exact_mod_cast hr0
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn'
  have hsn := sqrt_natCast_le n hn0
  have hnr : (n : ℝ) ≤ 3 * (halfDegree n : ℝ) := by
    exact_mod_cast (show n ≤ 3 * halfDegree n by dsimp [halfDegree]; omega)
  have hx := sqrt_degree_le_saddleScale_sq n hn2
  let f := ((n : ℝ) + 1 / 2) * Real.log n - n + (1 / 2) * Real.log (2 * Real.pi)
  let g := (gaussianPower (halfDegree n) : ℝ) * Real.log 2 +
    Real.log (gaussianKappa (halfDegree n))
  let a := criticalPolynomial (saddleRadius (halfDegree n)) -
    (halfDegree n : ℝ) * Real.log (saddleRadius (halfDegree n)) +
    (parity n : ℝ) * Real.log (1 + saddleRadius (halfDegree n) / 6) -
    Real.log (2 * Real.pi * saddleVariance (saddleRadius (halfDegree n))) / 2
  let b := (halfDegree n : ℝ) / 4 - (halfDegree n : ℝ) * Real.log (saddleScale (halfDegree n)) +
    saddleScale (halfDegree n) ^ 2 / 6 + saddleScale (halfDegree n) / 2 - 4 / 3 -
    Real.log (8 * Real.pi * (halfDegree n : ℝ)) / 2 +
    (parity n : ℝ) * Real.log (saddleScale (halfDegree n) / 6) +
    (6 * (parity n : ℝ) - 4) / saddleScale (halfDegree n)
  have hF : |Real.log (n.factorial : ℝ) - f| ≤ 1 / Real.sqrt (n : ℝ) := by
    apply (log_factorial_stirling_error n hn0).trans
    exact one_div_le_one_div_of_le hs (by linarith)
  have hG' : |Real.log (binaryGaussianSum (halfDegree n) : ℝ) - g| ≤
      6 / Real.sqrt (n : ℝ) := by
    apply (show |Real.log (binaryGaussianSum (halfDegree n) : ℝ) - g| ≤
      2 / (halfDegree n : ℝ) by simpa [g, sub_add_eq_sub_sub] using hG _ hrG).trans
    apply (div_le_div_iff₀ hr' hs).mpr
    linarith
  have hε1 : (parity n : ℝ) ≤ 1 := by
    exact_mod_cast (show parity n ≤ 1 by have := parity_lt_two n; omega)
  have hS : |a - b| ≤ 1000256 / Real.sqrt (n : ℝ) := by
    apply (saddleLog_firstCorrection_explicit (halfDegree n) hr683 (parity n)
      (by positivity) hε1).trans
    exact div_le_div_of_nonneg_left (by norm_num) hs hx
  have hid : Real.log (saddleBenchmark n) - elementaryLogModel n =
      (Real.log (n.factorial : ℝ) - f) +
        (Real.log (binaryGaussianSum (halfDegree n) : ℝ) - g) + (a - b) := by
    rw [log_saddleBenchmark n hn2]
    dsimp [elementaryLogModel, f, g, a, b]
    ring
  rw [hid]
  calc
    _ ≤ |Real.log (n.factorial : ℝ) - f| +
        |Real.log (binaryGaussianSum (halfDegree n) : ℝ) - g| + |a - b| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 1 / Real.sqrt (n : ℝ) + 6 / Real.sqrt (n : ℝ) +
        1000256 / Real.sqrt (n : ℝ) := add_le_add (add_le_add hF hG') hS
    _ = 1000263 / Real.sqrt (n : ℝ) := by ring

/-- The first correction in logarithmic form, with exactly the approved
elementary benchmark and a bound uniform in all four residue classes. -/
theorem saddleElementary_log_error :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      |Real.log (saddleBenchmark n / elementaryBenchmark n) - firstCorrection n| ≤
        K / Real.sqrt (n : ℝ) := by
  obtain ⟨N1, hN1, h1⟩ := log_saddleBenchmark_model_error
  obtain ⟨C, hC, N2, _, h2⟩ := elementaryLogModel_error
  refine ⟨1000263 + C, by positivity, max N1 N2, hN1.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hn1 := (le_max_left N1 N2).trans hn
  have hn2 := (le_max_right N1 N2).trans hn
  rw [Real.log_div (saddleBenchmark_pos n).ne' (elementary_positive n).ne']
  calc
    _ = |(Real.log (saddleBenchmark n) - elementaryLogModel n) +
        (elementaryLogModel n - Real.log (elementaryBenchmark n) - firstCorrection n)| := by ring_nf
    _ ≤ |Real.log (saddleBenchmark n) - elementaryLogModel n| +
        |elementaryLogModel n - Real.log (elementaryBenchmark n) - firstCorrection n| := abs_add_le _ _
    _ ≤ 1000263 / Real.sqrt (n : ℝ) + C / Real.sqrt (n : ℝ) :=
      add_le_add (h1 n hn1) (h2 n hn2)
    _ = (1000263 + C) / Real.sqrt (n : ℝ) := by ring

/-- The elementary expansion of the positive-saddle benchmark. -/
theorem saddleElementaryBenchmarkEstimate :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      |saddleBenchmark n / elementaryBenchmark n - 1 - firstCorrection n| ≤
        K / Real.sqrt (n : ℝ) :=
  relative_firstCorrection_of_log_bound saddleBenchmark saddleBenchmark_pos saddleElementary_log_error

/-- The elementary expansion of the exact coefficient benchmark requires
no subgroup-counting hypothesis. -/
theorem elementaryBenchmarkEstimate : ElementaryBenchmarkEstimate := by
  obtain ⟨A, hA, N1, hN1, h1⟩ := saddleBenchmarkEstimate
  obtain ⟨B, hB, N2, _, h2⟩ := saddleElementaryBenchmarkEstimate
  refine ⟨A * (1 + 4 + B) + B, by positivity, max N1 N2,
    hN1.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hn1 := (le_max_left N1 N2).trans hn
  have hn2 := (le_max_right N1 N2).trans hn
  have hn0 : 0 < n := by omega
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hnlarge : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) :=
    (Real.le_sqrt (by norm_num) hn'.le).mpr (by simpa using hnlarge)
  have hfirst : |exactBenchmark n / saddleBenchmark n - 1| ≤ A / Real.sqrt (n : ℝ) :=
    (h1 n hn1).trans (div_le_div_of_nonneg_left hA.le (Real.sqrt_pos.mpr hn')
      (sqrt_natCast_le n hn0))
  exact relative_error_transfer_bound (saddleBenchmark_pos n).ne' hs1 hA.le hB.le
    hfirst (h2 n hn2) (abs_firstCorrection_le_four n)

/-- T3 requires no additional analytic hypothesis once T1 is proved. -/
theorem T3_of_T1 (hT1 : T1) : T3 :=
  T3_of_T1_and_elementaryBenchmarkEstimate hT1 elementaryBenchmarkEstimate

/-- With the analytic and definition obligations proved, the conjunction
of all three approved targets is equivalent to the remaining counting target. -/
theorem allTargets_iff_T1 : AllTargets ↔ T1 := by
  constructor
  · exact fun h => h.2.1
  · exact fun h => ⟨definitionChecks, h, T2_of_T1 h, T3_of_T1 h⟩

end SymmetricSubgroupAsymptotics
