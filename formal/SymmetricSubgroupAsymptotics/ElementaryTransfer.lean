import SymmetricSubgroupAsymptotics.AsymptoticTransfer
import SymmetricSubgroupAsymptotics.Constants
import SymmetricSubgroupAsymptotics.SaddleEstimates

/-!
# From logarithmic estimates to the elementary relative estimate

The square of the prescribed first correction is of the same order as the
allowed remainder.  This makes exponentiating a logarithmic estimate safe
without changing either the correction or the error rate.
-/

set_option autoImplicit false
noncomputable section

open Filter

namespace SymmetricSubgroupAsymptotics

/-- The rank fourth-root scale squared dominates the degree square root. -/
theorem sqrt_degree_le_saddleScale_sq (n : ℕ) (hn : 2 ≤ n) :
    Real.sqrt (n : ℝ) ≤ saddleScale (halfDegree n) ^ 2 := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnr : (n : ℝ) ≤ 3 * (halfDegree n : ℝ) := by
    exact_mod_cast (show n ≤ 3 * halfDegree n by dsimp [halfDegree]; omega)
  have hx4 := saddleScale_pow_four (halfDegree n)
  have hs := Real.sq_sqrt hn0
  nlinarith [Real.sqrt_nonneg (n : ℝ), sq_nonneg (saddleScale (halfDegree n) ^ 2),
    sq_nonneg (saddleScale (halfDegree n) ^ 2 - Real.sqrt (n : ℝ))]

theorem sqrt_natCast_le (n : ℕ) (hn : 0 < n) : Real.sqrt (n : ℝ) ≤ n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity), Real.sqrt_nonneg (n : ℝ)]

theorem firstCorrection_sq_le (n : ℕ) (hn : 0 < n) :
    firstCorrection n ^ 2 ≤ 16 / Real.sqrt (n : ℝ) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  let x : ℝ := (48 * (n : ℝ)) ^ (1 / 4 : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hx4 : x ^ 4 = 48 * (n : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast (by positivity) (1 / 4 : ℝ) 4]
    norm_num
  have hs := Real.sq_sqrt hn0.le
  have hden : Real.sqrt (n : ℝ) ≤ x ^ 2 := by
    nlinarith [Real.sqrt_nonneg (n : ℝ), sq_nonneg (x ^ 2 - Real.sqrt (n : ℝ))]
  have hnum := firstCorrection_numerator_bound n
  have hnum2 : (6 * (parity n : ℝ) - 4) ^ 2 ≤ 16 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) hnum 2
    norm_num [sq_abs] at hh
    exact hh
  change ((6 * (parity n : ℝ) - 4) / x) ^ 2 ≤ _
  rw [div_pow]
  exact (div_le_div_of_nonneg_right hnum2 (sq_nonneg x)).trans
    (div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hn0) hden)

/-- Exponentiating a small logarithmic error preserves its first-order term. -/
theorem exp_first_order_error {u c B d : ℝ} (hd : 1 ≤ d)
    (hu : |u| ≤ 1) (herr : |u - c| ≤ B / d) (hc : c ^ 2 ≤ 16 / d) :
    |Real.exp u - 1 - c| ≤ (32 + 2 * B ^ 2 + B) / d := by
  have hd0 : 0 < d := by linarith
  have he2 : (u - c) ^ 2 ≤ (B / d) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (u - c)) herr 2
  have hdd : 1 / d ^ 2 ≤ 1 / d := by
    apply one_div_le_one_div_of_le hd0
    nlinarith
  have hu2 : u ^ 2 ≤ (32 + 2 * B ^ 2) / d := by
    have hbd : (B / d) ^ 2 ≤ B ^ 2 / d := by
      rw [div_pow, div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (by simpa using hdd) (sq_nonneg B)
    calc
      u ^ 2 ≤ 2 * c ^ 2 + 2 * (u - c) ^ 2 := by nlinarith [sq_nonneg (u - 2 * c)]
      _ ≤ 2 * (16 / d) + 2 * (B ^ 2 / d) := by linarith
      _ = (32 + 2 * B ^ 2) / d := by ring
  calc
    |Real.exp u - 1 - c| = |(Real.exp u - 1 - u) + (u - c)| := by ring_nf
    _ ≤ |Real.exp u - 1 - u| + |u - c| := abs_add_le _ _
    _ ≤ u ^ 2 + B / d := add_le_add (Real.abs_exp_sub_one_sub_id_le hu) herr
    _ ≤ (32 + 2 * B ^ 2) / d + B / d := by linarith only [hu2]
    _ = (32 + 2 * B ^ 2 + B) / d := by ring

/-- Any positive benchmark with the approved logarithmic expansion has the
approved relative expansion, with a uniform square-root remainder. -/
theorem relative_firstCorrection_of_log_bound (F : ℕ → ℝ)
    (hF : ∀ n, 0 < F n)
    (hlog : ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      |Real.log (F n / elementaryBenchmark n) - firstCorrection n| ≤
        B / Real.sqrt (n : ℝ)) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      |F n / elementaryBenchmark n - 1 - firstCorrection n| ≤
        K / Real.sqrt (n : ℝ) := by
  obtain ⟨B, hB, N, hN, hbound⟩ := hlog
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop, B / Real.sqrt (n : ℝ) ≤ (1 / 2 : ℝ) := by
    have hh : Tendsto (fun n : ℕ => B / Real.sqrt (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hsqrt
    exact (hh.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)).mono
      fun _ h => h.le
  have hcsmall : ∀ᶠ n : ℕ in atTop, |firstCorrection n| ≤ (1 / 2 : ℝ) := by
    exact ((firstCorrection_tendsto_zero.abs).eventually_lt_const
      (by norm_num : |(0 : ℝ)| < 1 / 2)).mono fun _ h => h.le
  obtain ⟨N', hsmall'⟩ := eventually_atTop.mp (hsmall.and hcsmall)
  refine ⟨32 + 2 * B ^ 2 + B, by positivity, max N N', hN.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hnN := (le_max_left N N').trans hn
  have hnN' := (le_max_right N N').trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).mpr
    (by simpa using hn1)
  have hu : |Real.log (F n / elementaryBenchmark n)| ≤ 1 := by
    calc
      _ ≤ |Real.log (F n / elementaryBenchmark n) - firstCorrection n| +
          |firstCorrection n| := by
        simpa using abs_add_le (Real.log (F n / elementaryBenchmark n) - firstCorrection n)
          (firstCorrection n)
      _ ≤ 1 := by linarith [(hsmall' n hnN').1, (hsmall' n hnN').2, hbound n hnN]
  have hh := exp_first_order_error hs1 hu (hbound n hnN)
    (firstCorrection_sq_le n (by omega))
  rwa [Real.exp_log (div_pos (hF n) (elementary_positive n))] at hh

/-- The logarithm of the saddle benchmark splits into its four elementary
factors, with the positive square root contributing one half of a logarithm. -/
theorem log_saddleBenchmark (n : ℕ) (hn : 2 ≤ n) :
    Real.log (saddleBenchmark n) =
      Real.log (n.factorial : ℝ) + Real.log (binaryGaussianSum (halfDegree n) : ℝ) +
      (parity n : ℝ) * Real.log (1 + saddleRadius (halfDegree n) / 6) +
      (criticalPolynomial (saddleRadius (halfDegree n)) -
        (halfDegree n : ℝ) * Real.log (saddleRadius (halfDegree n))) -
      (1 / 2 : ℝ) * Real.log (2 * Real.pi * saddleVariance (saddleRadius (halfDegree n))) := by
  have hr : 0 < halfDegree n := by dsimp [halfDegree]; omega
  have hρ := saddleRadius_pos (halfDegree n) hr
  have hb := saddleVariance_saddleRadius_pos (halfDegree n) hr
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hG : 0 < (binaryGaussianSum (halfDegree n) : ℝ) := by
    exact_mod_cast binaryGaussianSum_pos (halfDegree n)
  rw [saddleBenchmark, if_neg (not_lt.mpr hn)]
  dsimp
  rw [Real.log_div (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hf.ne' hG.ne']
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_sqrt (by positivity)]
  ring

end SymmetricSubgroupAsymptotics
