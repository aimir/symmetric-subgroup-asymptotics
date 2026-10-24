import SymmetricSubgroupAsymptotics.TinyComplementOddSmallDimensionMargins

/-! Uniform zero-matching margins for the remaining small odd primary.
For a nonpure top the actual complementary factor is at least two, so
the ceiling rounding costs at most half a primary unit. This is retained
in the dimension-one/two estimates instead of a free full unit. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TinyComplementOddZeroSmallMargins

theorem three_five_envelope_le (M C L : ℝ) (hM : 5 ≤ M)
    (hC0 : 0 ≤ C) (hC : C ≤ 8) (hL : 2 ≤ L) (hL6 : L ≤ 6) :
    ((C+1)/M)*Real.sqrt (3+L)+Real.sqrt (1+3/L) ≤ 8 := by
  have hrate : (C+1)/M ≤ (9/5 : ℝ) := by
    have hh := div_le_div_of_nonneg_left (by linarith only [hC0] : 0 ≤ C+1)
      (by norm_num : (0 : ℝ) < 5) hM
    linarith only [hh,hC]
  have hroot : Real.sqrt (3+L) ≤ (3 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hL6]
  have hmain := mul_le_mul hrate hroot (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9/5)
  have htop : Real.sqrt (1+3/L) ≤ (8/5 : ℝ) := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3)
      (by norm_num : (0 : ℝ) < 2) hL
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hh]
  linarith only [hmain,htop]

theorem two_five_nonpure_envelope_le (M C L : ℝ) (hM : 5 ≤ M)
    (hC0 : 0 ≤ C) (hC : C ≤ 4) (hL : 3 ≤ L) (hL6 : L ≤ 6) :
    ((C+1/2)/M)*Real.sqrt (2+L)+Real.sqrt (1+2/L) ≤ 4 := by
  have hrate : (C+1/2)/M ≤ (9/10 : ℝ) := by
    have hh := div_le_div_of_nonneg_left (by linarith only [hC0] : 0 ≤ C+1/2)
      (by norm_num : (0 : ℝ) < 5) hM
    linarith only [hh,hC]
  have hroot : Real.sqrt (2+L) ≤ (17/6 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hL6]
  have hmain := mul_le_mul hrate hroot (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9/10)
  have htop : Real.sqrt (1+2/L) ≤ (13/10 : ℝ) := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 3) hL
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hh]
  linarith only [hmain,htop]

theorem one_nonpure_envelope_le (M C L : ℝ) (hM : 5 ≤ M)
    (hC0 : 0 ≤ C) (hC : C ≤ 1) (hL : 13/4 ≤ L) (hL7 : L ≤ 7) :
    ((C+1/2)/M)*Real.sqrt (1+L)+Real.sqrt (1+1/L) ≤ 2 := by
  have hrate : (C+1/2)/M ≤ (3/10 : ℝ) := by
    have hh := div_le_div_of_nonneg_left (by linarith only [hC0] : 0 ≤ C+1/2)
      (by norm_num : (0 : ℝ) < 5) hM
    linarith only [hh,hC]
  have hroot : Real.sqrt (1+L) ≤ (17/6 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hL7]
  have hmain := mul_le_mul hrate hroot (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 3/10)
  have htop : Real.sqrt (1+1/L) ≤ (23/20 : ℝ) := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) < 13/4) hL
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hh]
  linarith only [hmain,htop]

end SymmetricSubgroupAsymptotics.TinyComplementOddZeroSmallMargins
