import SymmetricSubgroupAsymptotics.BinaryAffineThreeComplementEnvelope

/-! Dimension one for complementary power three. There is one exact
starting-exponent seed; every larger exponent uses the same uniform
Wallis and root-ratio argument. The total and matching charges remain
correlated, including the natural top-ceiling error. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineThreeComplementOneEnvelope
open BinaryAffineThreeComplementEnvelope BinaryAffineThreeComplementRootBounds

theorem envelope_le (a : ℕ) (ha : 7 ≤ a) (C m B u L : ℝ)
    (hm0 : 0 ≤ m) (hmC : m ≤ C) (hC : C ≤ 1) (hmA : m ≤ 1)
    (hB0 : 0 ≤ B) (hB : B ≤ 8/5) (hu0 : 0 ≤ u) (hu : u ≤ 35/128)
    (hwall : u^2*(3*(a : ℝ)+2) ≤ 2) (hL : 8 ≤ L) (hLupper : L ≤ (a : ℝ)+B) :
    (m*u+(C-m+1/3)/(2 : ℝ)^a)*Real.sqrt (1+L)+Real.sqrt (1+1/L) ≤ 2 := by
  have hrad : 1+L ≤ 1+(a : ℝ)+B := by linarith only [hLupper]
  have hfirst : u*Real.sqrt (1+L) ≤ 91/100 :=
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrad) hu0).trans
      (matching_one a B u hB0 hB hu0 hu hwall)
  have hrad' : 1+L ≤ (a : ℝ)+1+8/5 := by linarith only [hLupper,hB]
  have herror : Real.sqrt (1+L)/(2 : ℝ)^a ≤ 1/40 :=
    (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hrad') (by positivity)).trans
      (error_one a ha)
  have hmain := joint_scaled_le 1 C m u L ((2 : ℝ)^a) (91/100) (1/40)
    hm0 hmC (by simpa only [Nat.cast_one,one_pow] using hC)
      (by norm_num <;> assumption) (by norm_num) (by norm_num)
        (by simpa only [Nat.cast_one] using hfirst) (by simpa only [Nat.cast_one] using herror)
  have htop : Real.sqrt (1+1/L) ≤ 17/16 := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) < 8) hL
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    nlinarith only [hh]
  norm_num at hmain
  linarith only [hmain,htop]

theorem starting_envelope_le (C m u L : ℝ)
    (hm0 : 0 ≤ m) (hmC : m ≤ C) (hC : C ≤ 1) (hmA : m ≤ 1)
    (hu : u ≤ 5/16) (hL : 15/2 ≤ L) (hLupper : L ≤ 38/5) :
    (m*u+(C-m+1/3)/(2 : ℝ)^6)*Real.sqrt (1+L)+Real.sqrt (1+1/L) ≤ 2 := by
  have hroot : Real.sqrt (1+L) ≤ 47/16 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hLupper]
  have hfirst : u*Real.sqrt (1+L) ≤ 235/256 := by
    have hh := mul_le_mul hu hroot (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 5/16)
    norm_num at hh
    exact hh
  have herror : Real.sqrt (1+L)/(2 : ℝ)^6 ≤ 47/1024 := by
    have hh := div_le_div_of_nonneg_right hroot (by norm_num : (0 : ℝ) ≤ 64)
    convert hh using 1 <;> norm_num
  have hmain := joint_scaled_le 1 C m u L ((2 : ℝ)^6) (235/256) (47/1024)
    hm0 hmC (by simpa only [Nat.cast_one,one_pow] using hC)
      (by norm_num <;> assumption) (by norm_num) (by norm_num)
        (by simpa only [Nat.cast_one] using hfirst) (by simpa only [Nat.cast_one] using herror)
  have htop : Real.sqrt (1+1/L) ≤ 213/200 := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) < 15/2) hL
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    nlinarith only [hh]
  norm_num at hmain
  linarith only [hmain,htop]

end SymmetricSubgroupAsymptotics.BinaryAffineThreeComplementOneEnvelope
