import SymmetricSubgroupAsymptotics.Foundations

/-!
# Transfer from the exact benchmark to the analytic benchmarks

The analytic estimates below concern the explicit coefficient benchmark.
The transfer theorems require those estimates and T1. They do not assert
T2 or T3 without these hypotheses. Exponential absorption and the bound on
the stated first correction are proved here, rather than assumed.
-/

set_option autoImplicit false

open Filter

namespace SymmetricSubgroupAsymptotics

/-- The saddle estimate for the exact coefficient benchmark, independently
of the subgroup-counting estimate T1. -/
def SaddleBenchmarkEstimate : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    |exactBenchmark n / saddleBenchmark n - 1| ≤ K / (n : ℝ)

/-- The elementary estimate for the exact coefficient benchmark, retaining
the prescribed first correction and the square-root error denominator. -/
def ElementaryBenchmarkEstimate : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    |exactBenchmark n / elementaryBenchmark n - 1 - firstCorrection n| ≤
      K / Real.sqrt (n : ℝ)

/-- A decaying exponential is eventually bounded by any fixed reciprocal
real power, with coefficient one after increasing the threshold. -/
theorem eventually_exponential_le_inv_rpow {c : ℝ} (hc : 0 < c) (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ (-c * (n : ℝ)) ≤ 1 / (n : ℝ) ^ p := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ p *
      (2 : ℝ) ^ (-c * (n : ℝ))) atTop (nhds 0) := by
    convert (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p
      (c * Real.log 2) (mul_pos hc hlog)).comp tendsto_natCast_atTop_atTop using 1
    ext n
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 2
    ring
  filter_upwards [hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop 1] with n hn hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hnpos p)).mpr
  simpa [mul_comm] using hn.le

/-- The numerator in the prescribed correction has absolute value at most
four, uniformly across both parities. -/
theorem firstCorrection_numerator_bound (n : ℕ) :
    |6 * (parity n : ℝ) - 4| ≤ 4 := by
  rcases parity_cases n with h | h <;> norm_num [h]

/-- The first correction is uniformly bounded, including the totalized
value at degree zero. -/
theorem abs_firstCorrection_le_four (n : ℕ) : |firstCorrection n| ≤ 4 := by
  by_cases hn : n = 0
  · subst n
    norm_num [firstCorrection, parity]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have hden : 1 ≤ (48 * (n : ℝ)) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  rw [firstCorrection, abs_div, abs_of_nonneg (by positivity :
    0 ≤ (48 * (n : ℝ)) ^ (1 / 4 : ℝ))]
  apply (div_le_iff₀ (by linarith : 0 < (48 * (n : ℝ)) ^ (1 / 4 : ℝ))).mpr
  have := firstCorrection_numerator_bound n
  linarith

/-- An explicit degree-dependent upper bound for the correction. -/
theorem abs_firstCorrection_le_four_div_rpow (n : ℕ) :
    |firstCorrection n| ≤ 4 / (48 * (n : ℝ)) ^ (1 / 4 : ℝ) := by
  have hden : 0 ≤ (48 * (n : ℝ)) ^ (1 / 4 : ℝ) := by positivity
  rw [firstCorrection, abs_div, abs_of_nonneg hden]
  exact div_le_div_of_nonneg_right (firstCorrection_numerator_bound n) hden

/-- Despite its alternating numerator, the prescribed correction tends to
zero along all degrees. -/
theorem firstCorrection_tendsto_zero : Tendsto firstCorrection atTop (nhds 0) := by
  have hbase : Tendsto (fun n : ℕ => 48 * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun n : ℕ => (48 * (n : ℝ)) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hbase
  simpa only [firstCorrection, div_eq_mul_inv] using
    bdd_le_mul_tendsto_zero' 4 (Eventually.of_forall firstCorrection_numerator_bound)
      hden.inv_tendsto_atTop

/-- Algebraic transfer with a bounded correction. The first estimate is
measured relative to the nonzero intermediate benchmark `L`. -/
theorem relative_error_transfer_bound {s L M correction d A B D : ℝ}
    (hL : L ≠ 0) (hd : 1 ≤ d) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfirst : |s / L - 1| ≤ A / d)
    (hsecond : |L / M - 1 - correction| ≤ B / d)
    (hcorrection : |correction| ≤ D) :
    |s / M - 1 - correction| ≤ (A * (1 + D + B) + B) / d := by
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hBd : B / d ≤ B := (div_le_iff₀ hdpos).mpr (by nlinarith)
  have hratio : |L / M| ≤ 1 + D + B := by
    calc
      |L / M| = |(L / M - 1 - correction) + correction + 1| := by ring_nf
      _ ≤ |L / M - 1 - correction| + |correction| + |(1 : ℝ)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 1 + D + B := by norm_num at *; linarith
  have hidentity : s / M - 1 - correction =
      (s / L - 1) * (L / M) + (L / M - 1 - correction) := by
    have hcancel : s / L * (L / M) = s / M := div_mul_div_cancel₀ hL
    nlinarith
  rw [hidentity]
  calc
    |(s / L - 1) * (L / M) + (L / M - 1 - correction)| ≤
        |s / L - 1| * |L / M| + |L / M - 1 - correction| := by
      simpa only [abs_mul] using abs_add_le ((s / L - 1) * (L / M))
        (L / M - 1 - correction)
    _ ≤ (A / d) * (1 + D + B) + B / d :=
      add_le_add (mul_le_mul hfirst hratio (abs_nonneg _) (div_nonneg hA hdpos.le)) hsecond
    _ = (A * (1 + D + B) + B) / d := by ring

/-- T1 and the independent saddle benchmark estimate imply T2. -/
theorem T2_of_T1_and_saddleBenchmarkEstimate
    (hT1 : T1) (hSaddle : SaddleBenchmarkEstimate) : T2 := by
  obtain ⟨c, A, hc, hA, N1, hN1, hfirst⟩ := hT1
  obtain ⟨B, hB, N2, _, hsecond⟩ := hSaddle
  obtain ⟨N3, hdecay⟩ := eventually_atTop.mp (eventually_exponential_le_inv_rpow hc 1)
  refine ⟨A * (1 + B) + B, by positivity, max N1 (max N2 N3),
    hN1.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hn1 : N1 ≤ n := (le_max_left _ _).trans hn
  have hn2 : N2 ≤ n := (le_max_left N2 N3).trans ((le_max_right _ _).trans hn)
  have hn3 : N3 ≤ n := (le_max_right N2 N3).trans ((le_max_right _ _).trans hn)
  have hnlarge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hfirst' : |(subgroupCount n : ℝ) / exactBenchmark n - 1| ≤ A / (n : ℝ) := by
    calc
      _ ≤ A * (2 : ℝ) ^ (-c * (n : ℝ)) := hfirst n hn1
      _ ≤ A * (1 / (n : ℝ) ^ (1 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hdecay n hn3) hA.le
      _ = A / (n : ℝ) := by simp [div_eq_mul_inv]
  simpa using relative_error_transfer_bound (ne_of_gt (exactBenchmark_pos n))
    hnlarge hA.le hB.le hfirst' (by simpa using hsecond n hn2)
    (show |(0 : ℝ)| ≤ 0 by simp)

/-- T1 and the independent elementary benchmark estimate imply T3, with
the same explicit correction as in the approved target. -/
theorem T3_of_T1_and_elementaryBenchmarkEstimate
    (hT1 : T1) (hElementary : ElementaryBenchmarkEstimate) : T3 := by
  obtain ⟨c, A, hc, hA, N1, hN1, hfirst⟩ := hT1
  obtain ⟨B, hB, N2, _, hsecond⟩ := hElementary
  obtain ⟨N3, hdecay⟩ := eventually_atTop.mp
    (eventually_exponential_le_inv_rpow hc (1 / 2))
  refine ⟨A * (5 + B) + B, by positivity, max N1 (max N2 N3),
    hN1.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hn1 : N1 ≤ n := (le_max_left _ _).trans hn
  have hn2 : N2 ≤ n := (le_max_left N2 N3).trans ((le_max_right _ _).trans hn)
  have hn3 : N3 ≤ n := (le_max_right N2 N3).trans ((le_max_right _ _).trans hn)
  have hnlarge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hnlarge
  have hfirst' : |(subgroupCount n : ℝ) / exactBenchmark n - 1| ≤
      A / Real.sqrt (n : ℝ) := by
    calc
      _ ≤ A * (2 : ℝ) ^ (-c * (n : ℝ)) := hfirst n hn1
      _ ≤ A * (1 / (n : ℝ) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hdecay n hn3) hA.le
      _ = A / Real.sqrt (n : ℝ) := by rw [Real.sqrt_eq_rpow]; ring
  simpa only [show (1 : ℝ) + 4 = 5 by norm_num] using
    relative_error_transfer_bound (ne_of_gt (exactBenchmark_pos n))
    hsqrt hA.le hB.le hfirst' (hsecond n hn2) (abs_firstCorrection_le_four n)

end SymmetricSubgroupAsymptotics
