import SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementMargins

/-! The dimension-three companion uses the SAME actual total coefficient
8, including the translation head. This coefficient is not replaced by
7 or by an independent complement budget. The narrow rational margin
is uniform in the whole complementary interval v>=5. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementThreeMargin

theorem root_div_le (v : ℝ) (hv : 5 ≤ v) :
    Real.sqrt (9+(3/2)*v)/v ≤ (13/16 : ℝ) := by
  have hv0 : 0 < v := by linarith only [hv]
  have hprod : 0 ≤ (v-5)*(169*v+461) :=
    mul_nonneg (by linarith only [hv]) (by positivity)
  apply (sq_le_sq₀ (div_nonneg (Real.sqrt_nonneg _) hv0.le) (by norm_num)).mp
  rw [div_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 9+(3/2)*v)]
  apply (div_le_iff₀ (pow_pos hv0 2)).mpr
  nlinarith only [hprod]

theorem envelope_le (v C L : ℝ) (hv : 5 ≤ v) (hC0 : 0 ≤ C) (hC : C ≤ 8)
    (hL : 9/2 ≤ L) (hentropy : L ≤ 6+(3/2)*v) :
    (C/v+1/v^2)*Real.sqrt (3+L)+Real.sqrt (1+3/L) ≤ 8 := by
  have hv0 : 0 < v := by linarith only [hv]
  have hroot : Real.sqrt (3+L)/v ≤ (13/16 : ℝ) :=
    (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt
      (by linarith only [hentropy] : 3+L ≤ 9+(3/2)*v)) hv0.le).trans
        (root_div_le v hv)
  have hinv : 1/v ≤ (1/5 : ℝ) := one_div_le_one_div_of_le (by norm_num) hv
  have hmain : (C/v+1/v^2)*Real.sqrt (3+L) ≤ (533/80 : ℝ) := by
    have hfirst := mul_le_mul_of_nonneg_left hroot (show 0 ≤ C+1/v by positivity)
    have hsecond := mul_le_mul_of_nonneg_right (add_le_add hC hinv)
      (by norm_num : (0 : ℝ) ≤ 13/16)
    have hh := hfirst.trans hsecond
    convert hh using 1
    · field_simp [hv0.ne']
    · norm_num
  have htop : Real.sqrt (1+3/L) ≤ (4/3 : ℝ) := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3)
      (by norm_num : (0 : ℝ) < 9/2) hL
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hh]
  linarith only [hmain,htop]

end SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementThreeMargin
