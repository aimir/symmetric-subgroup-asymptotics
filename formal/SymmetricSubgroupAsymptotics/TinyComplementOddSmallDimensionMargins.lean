import SymmetricSubgroupAsymptotics.TinyComplementOddMargins

/-! Whole lower-dimensional odd-primary intervals. Every estimate
optimizes the matching and remaining charges of the SAME order. The
small constants are proved by rational square comparisons; no top
representatives, finite action catalogue or fitted conclusion is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TinyComplementOddSmallDimensionMargins
open TinyComplementOddMargins

theorem three_envelope_le (M m C u L : ℝ)
    (hM : 7 ≤ M) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hmC : m ≤ C) (hC : C ≤ 8)
    (hu : u ≤ 1/2) (hL : 2 ≤ L) (hL10 : L ≤ 10) :
    (m*u+(C-m+1)/M)*Real.sqrt (3+L)+Real.sqrt (1+3/L) ≤ 8 := by
  have hrate : m*u+(C-m+1)/M ≤ (23/14 : ℝ) := by
    have hh := joint_rate_le M 7 m C 1 8 u (by norm_num) hM hm0 hm1 hmC hC hu
    convert hh using 1 <;> norm_num
  have hroot : Real.sqrt (3+L) ≤ (15/4 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hL10]
  have hmain := mul_le_mul hrate hroot (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 23/14)
  have htop : Real.sqrt (1+3/L) ≤ (8/5 : ℝ) := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3)
      (by norm_num : (0 : ℝ) < 2) hL
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hh]
  linarith only [hmain,htop]

theorem two_zero_envelope_le (M C L : ℝ) (hM : 7 ≤ M) (hC0 : 0 ≤ C) (hC : C ≤ 4)
    (hL : 2 ≤ L) (hL10 : L ≤ 10) :
    ((C+1)/M)*Real.sqrt (2+L)+Real.sqrt (1+2/L) ≤ 4 := by
  have hrate : (C+1)/M ≤ (5/7 : ℝ) := by
    calc
      (C+1)/M = 0*0+(C-0+1)/M := by ring
      _ ≤ 0/2+(4-0+1)/7 := joint_rate_le M 7 0 C 0 4 0 (by norm_num) hM
        le_rfl le_rfl hC0 hC (by norm_num)
      _ = 5/7 := by norm_num
  have hroot : Real.sqrt (2+L) ≤ (7/2 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hL10]
  have hmain := mul_le_mul hrate hroot (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 5/7)
  have htop : Real.sqrt (1+2/L) ≤ (3/2 : ℝ) := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 2) hL
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hh]
  linarith only [hmain,htop]

theorem two_large_envelope_le (M m C u L : ℝ)
    (hM : 16 ≤ M) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hmC : m ≤ C) (hC : C ≤ 4)
    (hu : u ≤ 1/2) (hL : 3 ≤ L) (hL7 : L ≤ 7) :
    (m*u+(C-m+1)/M)*Real.sqrt (2+L)+Real.sqrt (1+2/L) ≤ 4 := by
  have hrate : m*u+(C-m+1)/M ≤ (3/4 : ℝ) := by
    have hh := joint_rate_le M 16 m C 1 4 u (by norm_num) hM hm0 hm1 hmC hC hu
    convert hh using 1 <;> norm_num
  have hroot : Real.sqrt (2+L) ≤ (3 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hL7]
  have hmain := mul_le_mul hrate hroot (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 3/4)
  have htop : Real.sqrt (1+2/L) ≤ (4/3 : ℝ) := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 3) hL
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hh]
  linarith only [hmain,htop]

theorem two_short_envelope_le (M m C u L : ℝ)
    (hM : 9 ≤ M) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hmC : m ≤ C) (hC : C ≤ 4)
    (hu : u ≤ 1/2) (hL : 3 ≤ L) (hL6 : L ≤ 6) :
    (m*u+(C-m+1)/M)*Real.sqrt (2+L)+Real.sqrt (1+2/L) ≤ 4 := by
  have hrate : m*u+(C-m+1)/M ≤ (17/18 : ℝ) := by
    have hh := joint_rate_le M 9 m C 1 4 u (by norm_num) hM hm0 hm1 hmC hC hu
    convert hh using 1 <;> norm_num
  have hroot : Real.sqrt (2+L) ≤ (17/6 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hL6]
  have hmain := mul_le_mul hrate hroot (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 17/18)
  have htop : Real.sqrt (1+2/L) ≤ (13/10 : ℝ) := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 3) hL
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hh]
  linarith only [hmain,htop]

end SymmetricSubgroupAsymptotics.TinyComplementOddSmallDimensionMargins
