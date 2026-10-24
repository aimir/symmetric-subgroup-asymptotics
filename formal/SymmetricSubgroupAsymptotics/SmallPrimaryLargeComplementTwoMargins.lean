import SymmetricSubgroupAsymptotics.MixedInverseSqrtEndpointBound
import SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementThreeMargin

/-! Three coefficient intervals for the dimension-two SAME chief order.
The actual total is four; the matching coefficient is at most three,
or at most one on the short odd interval. A convex-square endpoint
argument retains the common complementary variable, including the
natural-ceiling error. No top-degree census or fitting premise occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementTwoMargins
open MixedInverseSqrtEndpointBound

theorem joint_rate_le (M N v m C A B : ℝ) (hN : 0 < N) (hv : 0 < v)
    (hNM : N ≤ M) (hvM : v ≤ M) (hm : m ≤ A) (hC : C ≤ B) (hAB : A ≤ B) :
    m/v+(C-m)/M+1/(M*v) ≤ (A+1/N)/v+(B-A)/N := by
  have hM : 0 < M := hN.trans_le hNM
  have hslope : 0 ≤ 1/v-1/M := sub_nonneg.mpr (one_div_le_one_div_of_le hv hvM)
  have hh := add_le_add (mul_le_mul_of_nonneg_right hm hslope)
    (div_le_div_of_nonneg_right hC hM.le)
  have hfirst : m/v+(C-m)/M ≤ A/v+(B-A)/M := by
    convert hh using 1 <;> ring
  have hsecond := div_le_div_of_nonneg_left (sub_nonneg.mpr hAB) hN hNM
  have hthird : 1/(M*v) ≤ 1/(N*v) :=
    one_div_le_one_div_of_le (mul_pos hN hv) (mul_le_mul_of_nonneg_right hNM hv.le)
  calc
    m/v+(C-m)/M+1/(M*v) ≤ A/v+(B-A)/M+1/(N*v) := add_le_add hfirst hthird
    _ ≤ A/v+(B-A)/N+1/(N*v) := add_le_add (add_le_add le_rfl hsecond) le_rfl
    _ = (A+1/N)/v+(B-A)/N := by field_simp [hN.ne',hv.ne']; ring

private theorem mixed_le_of_square (a b c k x R : ℝ)
    (hcoef : 0 ≤ a/x+b) (hrad : 0 ≤ c+k*x) (hR : 0 ≤ R)
    (hsq : (a/x+b)^2*(c+k*x) ≤ R^2) : mixed a b c k x ≤ R := by
  apply (sq_le_sq₀ (mul_nonneg hcoef (Real.sqrt_nonneg _)) hR).mp
  simpa only [mixed,mul_pow,Real.sq_sqrt hrad] using hsq

private theorem top_le (L : ℝ) (hL : 9/2 ≤ L) : Real.sqrt (1+2/L) ≤ (11/9 : ℝ) := by
  have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ) < 9/2) hL
  apply Real.sqrt_le_iff.mpr
  refine ⟨by norm_num,?_⟩
  linarith only [hh]

private theorem large_mixed_le (v : ℝ) (hv : 5 ≤ v) (hv63 : v ≤ 63) :
    mixed (49/16) (1/16) 8 (3/2) v ≤ (11/4 : ℝ) := by
  have hh := le_max_endpoints (49/16) (1/16) 8 (3/2) 5 63 v
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv hv63
  have hl : mixed (49/16) (1/16) 8 (3/2) 5 ≤ (11/4 : ℝ) :=
    mixed_le_of_square _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hr : mixed (49/16) (1/16) 8 (3/2) 63 ≤ (11/4 : ℝ) :=
    mixed_le_of_square _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact hh.trans (max_le hl hr)

private theorem binary_mixed_le (v : ℝ) (hv : 5 ≤ v) (hv8 : v ≤ 8) :
    mixed (25/8) (1/8) 5 (3/2) v ≤ (11/4 : ℝ) := by
  have hh := le_max_endpoints (25/8) (1/8) 5 (3/2) 5 8 v
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv hv8
  have hl : mixed (25/8) (1/8) 5 (3/2) 5 ≤ (11/4 : ℝ) :=
    mixed_le_of_square _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hr : mixed (25/8) (1/8) 5 (3/2) 8 ≤ (11/4 : ℝ) :=
    mixed_le_of_square _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact hh.trans (max_le hl hr)

private theorem odd_mixed_le (v : ℝ) (hv : 5 ≤ v) (hv9 : v ≤ 9) :
    mixed (8/7) (3/7) 6 (3/2) v ≤ (11/4 : ℝ) := by
  have hh := le_max_endpoints (8/7) (3/7) 6 (3/2) 5 9 v
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv hv9
  have hl : mixed (8/7) (3/7) 6 (3/2) 5 ≤ (11/4 : ℝ) :=
    mixed_le_of_square _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hr : mixed (8/7) (3/7) 6 (3/2) 9 ≤ (11/4 : ℝ) :=
    mixed_le_of_square _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact hh.trans (max_le hl hr)

theorem large_primary_envelope_le (M v m C L : ℝ)
    (hM : 16 ≤ M) (hv : 5 ≤ v) (hvM : v ≤ M) (hv63 : v ≤ 63)
    (hm : m ≤ 3) (hC : C ≤ 4) (hL : 9/2 ≤ L) (hentropy : L ≤ 6+(3/2)*v) :
    (m/v+(C-m)/M+1/(M*v))*Real.sqrt (2+L)+Real.sqrt (1+2/L) ≤ 4 := by
  have hrate := joint_rate_le M 16 v m C 3 4 (by norm_num) (by linarith only [hv])
    hM hvM hm hC (by norm_num)
  have hmain : (m/v+(C-m)/M+1/(M*v))*Real.sqrt (2+L) ≤ (11/4 : ℝ) := by
    have hh := mul_le_mul hrate
      (Real.sqrt_le_sqrt (by linarith only [hentropy] : 2+L ≤ 8+(3/2)*v))
      (Real.sqrt_nonneg _) (by positivity : 0 ≤ (3+1/(16 : ℝ))/v+(4-3)/16)
    have heq : (3+1/(16 : ℝ))/v+(4-3)/16 = (49/16 : ℝ)/v+1/16 := by ring
    rw [heq] at hh
    exact hh.trans (large_mixed_le v hv hv63)
  linarith only [hmain,top_le L hL]

theorem binary_eight_envelope_le (v m C L : ℝ)
    (hv : 5 ≤ v) (hv8 : v ≤ 8) (hm : m ≤ 3) (hC : C ≤ 4)
    (hL : 9/2 ≤ L) (hentropy : L ≤ 3+(3/2)*v) :
    (m/v+(C-m)/8+1/(8*v))*Real.sqrt (2+L)+Real.sqrt (1+2/L) ≤ 4 := by
  have hrate := joint_rate_le 8 8 v m C 3 4 (by norm_num) (by linarith only [hv])
    le_rfl hv8 hm hC (by norm_num)
  have hmain : (m/v+(C-m)/8+1/(8*v))*Real.sqrt (2+L) ≤ (11/4 : ℝ) := by
    have hh := mul_le_mul hrate
      (Real.sqrt_le_sqrt (by linarith only [hentropy] : 2+L ≤ 5+(3/2)*v))
      (Real.sqrt_nonneg _) (by positivity : 0 ≤ (3+1/(8 : ℝ))/v+(4-3)/8)
    have heq : (3+1/(8 : ℝ))/v+(4-3)/8 = (25/8 : ℝ)/v+1/8 := by ring
    rw [heq] at hh
    exact hh.trans (binary_mixed_le v hv hv8)
  linarith only [hmain,top_le L hL]

theorem odd_short_envelope_le (M v m C L : ℝ)
    (hM : 7 ≤ M) (hv : 5 ≤ v) (hvM : v ≤ M) (hv9 : v ≤ 9)
    (hm : m ≤ 1) (hC : C ≤ 4) (hL : 9/2 ≤ L) (hentropy : L ≤ 4+(3/2)*v) :
    (m/v+(C-m)/M+1/(M*v))*Real.sqrt (2+L)+Real.sqrt (1+2/L) ≤ 4 := by
  have hrate := joint_rate_le M 7 v m C 1 4 (by norm_num) (by linarith only [hv])
    hM hvM hm hC (by norm_num)
  have hmain : (m/v+(C-m)/M+1/(M*v))*Real.sqrt (2+L) ≤ (11/4 : ℝ) := by
    have hh := mul_le_mul hrate
      (Real.sqrt_le_sqrt (by linarith only [hentropy] : 2+L ≤ 6+(3/2)*v))
      (Real.sqrt_nonneg _) (by positivity : 0 ≤ (1+1/(7 : ℝ))/v+(4-1)/7)
    have heq : (1+1/(7 : ℝ))/v+(4-1)/7 = (8/7 : ℝ)/v+3/7 := by ring
    rw [heq] at hh
    exact hh.trans (odd_mixed_le v hv hv9)
  linarith only [hmain,top_le L hL]

end SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementTwoMargins
