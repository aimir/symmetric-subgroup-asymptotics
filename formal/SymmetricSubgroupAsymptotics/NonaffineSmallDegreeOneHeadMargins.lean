import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! Three scalar intervals for a ONE strict-coset head in local degrees
32..127. The intervals control only real logarithms and square roots;
there are no finite actions, model rows or fitted group hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NonaffineSmallDegreeOneHeadMargins

private theorem of_band (r lo : ℕ) (L U c1 c4 : ℝ) (hr : lo ≤ r)
    (hL : 0 ≤ L) (hLU : L ≤ U) (hc1 : 0 ≤ c1) (hc4 : 0 ≤ c4)
    (hsq1 : U+1 ≤ c1^2) (hsq4 : U+4 ≤ c4^2)
    (h1 : (U+6)/2*c1 ≤ 9*(lo : ℝ)/20)
    (h2 : ((U+5)/2+1/3)*c4 ≤ 11*(lo : ℝ)/20)
    (h3 : c1/2+(U+4)/2*c4 ≤ 29*(lo : ℝ)/40) :
    (L+6)/2*Real.sqrt (L+1) ≤ 9*(r : ℝ)/20 ∧
    ((L+5)/2+1/3)*Real.sqrt (L+4) ≤ 11*(r : ℝ)/20 ∧
    Real.sqrt (L+1)/2+(L+4)/2*Real.sqrt (L+4) ≤ 29*(r : ℝ)/40 := by
  have hroot1 : Real.sqrt (L+1) ≤ c1 := Real.sqrt_le_iff.mpr
    ⟨hc1,by linarith only [hLU,hsq1]⟩
  have hroot4 : Real.sqrt (L+4) ≤ c4 := Real.sqrt_le_iff.mpr
    ⟨hc4,by linarith only [hLU,hsq4]⟩
  have hp1 := mul_le_mul (show (L+6)/2 ≤ (U+6)/2 by linarith only [hLU]) hroot1
    (Real.sqrt_nonneg (L+1)) (by linarith only [hL,hLU] : 0 ≤ (U+6)/2)
  have hp2 := mul_le_mul (show (L+5)/2+1/3 ≤ (U+5)/2+1/3 by linarith only [hLU]) hroot4
    (Real.sqrt_nonneg (L+4)) (by linarith only [hL,hLU] : 0 ≤ (U+5)/2+1/3)
  have hp3 := mul_le_mul (show (L+4)/2 ≤ (U+4)/2 by linarith only [hLU]) hroot4
    (Real.sqrt_nonneg (L+4)) (by linarith only [hL,hLU] : 0 ≤ (U+4)/2)
  have hrR : (lo : ℝ) ≤ r := by exact_mod_cast hr
  exact ⟨by linarith only [hp1,h1,hrR],by linarith only [hp2,h2,hrR],
    by linarith only [hroot1,hp3,h3,hrR]⟩

/-- The three remainders correspond to top2, tops3..15, and tops>=16. -/
theorem margin_bounds (r : ℕ) (hr : 32 ≤ r) (hsmall : r < 128) :
    (Real.logb 2 (r : ℝ)+6)/2*Real.sqrt (Real.logb 2 (r : ℝ)+1) ≤ 9*(r : ℝ)/20 ∧
    ((Real.logb 2 (r : ℝ)+5)/2+1/3)*Real.sqrt (Real.logb 2 (r : ℝ)+4) ≤ 11*(r : ℝ)/20 ∧
    Real.sqrt (Real.logb 2 (r : ℝ)+1)/2+
      (Real.logb 2 (r : ℝ)+4)/2*Real.sqrt (Real.logb 2 (r : ℝ)+4) ≤ 29*(r : ℝ)/40 := by
  let L := Real.logb 2 (r : ℝ)
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (show 1 ≤ r by omega))
  by_cases h40 : r < 40
  · have hLU : L ≤ 16/3 := IntegerLogSquareRootCeilingCertificate.log_upper r 3 16
      (by omega) (by decide) ((Nat.pow_le_pow_left (show r ≤ 39 by omega) 3).trans (by decide))
    exact of_band r 32 L (16/3) (63/25) (31/10) hr hL hLU
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · by_cases h64 : r < 64
    · have hLU : L ≤ 6 := by
        have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 6 (by omega) (by decide)
          (by simpa only [pow_one] using (show r ≤ 2^6 by omega))
        simpa only [Nat.cast_one,div_one] using hh
      exact of_band r 40 L 6 (8/3) (16/5) (by omega) hL hLU
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
    · have hLU : L ≤ 7 := by
        have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 7 (by omega) (by decide)
          (by simpa only [pow_one] using (show r ≤ 2^7 by omega))
        simpa only [Nat.cast_one,div_one] using hh
      exact of_band r 64 L 7 3 (10/3) (by omega) hL hLU
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)

/-- Two root ratios used in the three top regimes, uniformly in L>=5. -/
theorem root_ratio_bounds (L : ℝ) (hL : 5 ≤ L) :
    Real.sqrt (L+1) ≤ (11/10 : ℝ)*Real.sqrt L ∧
    Real.sqrt (L+4) ≤ (27/20 : ℝ)*Real.sqrt L := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  constructor
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hL0,Real.sq_sqrt (by linarith only [hL] : 0 ≤ L+1)]
    nlinarith only [hL]
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hL0,Real.sq_sqrt (by linarith only [hL] : 0 ≤ L+4)]
    nlinarith only [hL]

end SymmetricSubgroupAsymptotics.NonaffineSmallDegreeOneHeadMargins
