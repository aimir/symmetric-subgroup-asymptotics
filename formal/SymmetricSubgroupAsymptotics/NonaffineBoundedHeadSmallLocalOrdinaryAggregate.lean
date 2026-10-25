import SymmetricSubgroupAsymptotics.ImprimitiveMinimumRateScaling
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! Shared small-local scalar bands for a literal ordinary socle head.
The head is paid ONCE, with the actual outer quotient's minimum-rate
coefficient and the rounded strictly-smaller top ceiling. The public
bounds state head/coefficient budgets, not an assumed fitting inequality.
No simple-generation, outer-order, or permutation-generator input is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NonaffineBoundedHeadSmallLocalOrdinaryAggregate
open ActualWreathChiefUnitMinimumRate

private theorem cost_of_constants (r t lo : ℕ) (hr : 2 ≤ r) (ht : 2 ≤ t) (hlo : lo ≤ r)
    (H b U Hmax Bmax c1 c4 : ℝ) (hH0 : 0 ≤ H) (hb0 : 0 ≤ b)
    (hH : H ≤ Hmax) (hb : b ≤ Bmax) (hLU : Real.logb 2 (r : ℝ) ≤ U)
    (hc1 : 0 ≤ c1) (hc4 : 0 ≤ c4) (hsq1 : U+1 ≤ c1^2) (hsq4 : U+4 ≤ c4^2)
    (hc : Hmax/2*c1+(Bmax+2)/2*c4 ≤ (lo : ℝ)) :
    H+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  let L := Real.logb 2 (r : ℝ)
  let e := Real.logb 2 (t : ℝ)
  let u1 := Real.sqrt (L+1)
  let u4 := Real.sqrt (L+4)
  let w := Real.sqrt (L+e)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (show 1 ≤ r by omega))
  have he : 0 < e := Real.logb_pos (by norm_num) (by linarith only [htR])
  have hw : 0 < w := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hL he)
  have hroot1 : u1 ≤ c1 := Real.sqrt_le_iff.mpr ⟨hc1,by linarith only [hLU,hsq1]⟩
  have hroot4 : u4 ≤ c4 := Real.sqrt_le_iff.mpr ⟨hc4,by linarith only [hLU,hsq4]⟩
  have hh1 := mul_le_mul hH hroot1 (Real.sqrt_nonneg (L+1))
    (show 0 ≤ Hmax by linarith only [hH0,hH])
  have hh4 := mul_le_mul (show b+2 ≤ Bmax+2 by linarith only [hb]) hroot4
    (Real.sqrt_nonneg (L+4)) (show 0 ≤ Bmax+2 by linarith only [hb0,hb])
  have hloR : (lo : ℝ) ≤ r := by exact_mod_cast hlo
  have hmargin : H/2*u1+(b+2)/2*u4 ≤ (r : ℝ) := by nlinarith only [hh1,hh4,hc,hloR]
  have hhead := mul_le_mul_of_nonneg_left
    (ImprimitiveTopLogarithmicScaling.sqrt_log_add_le_half_mul L hL t ht) hH0
  have htop := ImprimitiveMinimumRateScaling.ceiling_le_twice_rate t ht
  have hsource := mul_le_mul_of_nonneg_right htop (Real.sqrt_nonneg (L+e))
  have hrate := mul_le_mul_of_nonneg_left
    (ImprimitiveMinimumRateScaling.rate_mul_sqrt_log_add_le L hL t ht)
    (show 0 ≤ b+2 by linarith only [hb0])
  have hscaled := mul_le_mul_of_nonneg_left hmargin (show (0 : ℝ) ≤ t by positivity)
  rw [Real.logb_mul hrR.ne' (by linarith only [htR] : (t : ℝ) ≠ 0)]
  change H+b*rate t+traceyPermutationGeneratorCeiling t ≤ (r : ℝ)*(t : ℝ)/w
  apply (le_div_iff₀ hw).mpr
  nlinarith only [hhead,hsource,hrate,hscaled]

private theorem log_degree_le_five (r : ℕ) (hr : 2 ≤ r) (hsmall : r < 32) :
    Real.logb 2 (r : ℝ) ≤ 5 := by
  have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 5 (by omega) (by decide)
    (by simpa only [pow_one] using (show r ≤ 2^5 by omega))
  simpa only [Nat.cast_one,div_one] using hh

/-- Ten genuine ordinary head generators pay every top in local degrees
20..31. In degrees20..21 the actual outer coefficient must be at most
three; above that band four is enough. -/
theorem ten_generator_cost_le (r t : ℕ) (hr : 20 ≤ r) (hsmall : r < 32) (ht : 2 ≤ t)
    (H b : ℝ) (hH0 : 0 ≤ H) (hH : H ≤ 10) (hb0 : 0 ≤ b)
    (hb : b ≤ if r < 22 then 3 else 4) :
    H+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  have hLU := log_degree_le_five r (by omega) hsmall
  by_cases hl : r < 22
  · have hb3 : b ≤ 3 := by simpa only [if_pos hl] using hb
    exact cost_of_constants r t 20 (by omega) ht hr H b 5 10 3 (5/2) 3
      hH0 hb0 hH hb3 hLU (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · have hb4 : b ≤ 4 := by simpa only [if_neg hl] using hb
    exact cost_of_constants r t 22 (by omega) ht (by omega) H b 5 10 4 (5/2) 3
      hH0 hb0 hH hb4 hLU (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Seven genuine head generators and coefficient four pay every top in
local degrees18..31. This does not assert the missing lower-degree cases. -/
theorem seven_generator_cost_le (r t : ℕ) (hr : 18 ≤ r) (hsmall : r < 32) (ht : 2 ≤ t)
    (H b : ℝ) (hH0 : 0 ≤ H) (hH : H ≤ 7) (hb0 : 0 ≤ b) (hb : b ≤ 4) :
    H+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  exact cost_of_constants r t 18 (by omega) ht hr H b 5 7 4 (5/2) 3
    hH0 hb0 hH hb (log_degree_le_five r (by omega) hsmall)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end SymmetricSubgroupAsymptotics.NonaffineBoundedHeadSmallLocalOrdinaryAggregate
