import SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementTwoMargins

/-! A dimension-one interval with the actual total multiplicity one.
Keeping the matching and remaining charges joint leaves no constant
1/M term after maximization. A single root-ratio bound then pays the
whole complementary interval, including the actual ceiling error. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementOneMargin

theorem root_div_le (v : ℝ) (hv : 5 ≤ v) :
    Real.sqrt (7+(3/2)*v)/v ≤ (7/9 : ℝ) := by
  have hv0 : 0 < v := by linarith only [hv]
  have hprod : 0 ≤ (v-5)*(98*v+247) :=
    mul_nonneg (by linarith only [hv]) (by positivity)
  apply (sq_le_sq₀ (div_nonneg (Real.sqrt_nonneg _) hv0.le) (by norm_num)).mp
  rw [div_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 7+(3/2)*v)]
  apply (div_le_iff₀ (pow_pos hv0 2)).mpr
  nlinarith only [hprod]

theorem envelope_le (M v m C L : ℝ)
    (hM : 7 ≤ M) (hv : 5 ≤ v) (hvM : v ≤ M) (hm : m ≤ 1) (hC : C ≤ 1)
    (hL : 9/2 ≤ L) (hentropy : L ≤ 6+(3/2)*v) :
    (m/v+(C-m)/M+1/(M*v))*Real.sqrt (1+L)+Real.sqrt (1+1/L) ≤ 2 := by
  have hv0 : 0 < v := by linarith only [hv]
  have hrate := SmallPrimaryLargeComplementTwoMargins.joint_rate_le M 7 v m C 1 1
    (by norm_num) hv0 hM hvM hm hC le_rfl
  have hrate' : m/v+(C-m)/M+1/(M*v) ≤ (8/7 : ℝ)/v := by
    convert hrate using 1 <;> ring
  have hroot : Real.sqrt (1+L)/v ≤ (7/9 : ℝ) :=
    (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt
      (by linarith only [hentropy] : 1+L ≤ 7+(3/2)*v)) hv0.le).trans
        (root_div_le v hv)
  have hmain : (m/v+(C-m)/M+1/(M*v))*Real.sqrt (1+L) ≤ (8/9 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hrate' (Real.sqrt_nonneg (1+L))
    have hs := mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 8/7)
    have heq : (8/7 : ℝ)/v*Real.sqrt (1+L) = (8/7)* (Real.sqrt (1+L)/v) := by ring
    rw [heq] at hh
    calc
      _ ≤ (8/7 : ℝ)*(7/9) := hh.trans hs
      _ = (8/9 : ℝ) := by norm_num
  have htop : Real.sqrt (1+1/L) ≤ (10/9 : ℝ) := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) < 9/2) hL
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hh]
  linarith only [hmain,htop]

end SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementOneMargin
