import SymmetricSubgroupAsymptotics.ImprimitiveMinimumRateScaling
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! A genuine ordinary head of at most eight generators and quotient
coefficient at most three fit local degrees24..31 for every top. This
shared band retains the rounded coarse top ceiling. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NonaffineEightGeneratorSmallDegreeOrdinaryAggregate
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

theorem eight_generator_cost_le (r t : ℕ) (hr : 24 ≤ r) (hsmall : r < 32) (ht : 2 ≤ t)
    (H b : ℝ) (hH0 : 0 ≤ H) (hH : H ≤ 8) (hb0 : 0 ≤ b) (hb : b ≤ 3) :
    H+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  have hLU : Real.logb 2 (r : ℝ) ≤ 5 := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 5 (by omega) (by decide)
      (by simpa only [pow_one] using (show r ≤ 2^5 by omega))
    simpa only [Nat.cast_one,div_one] using hh
  exact cost_of_constants r t 24 (by omega) ht hr H b 5 8 3 (5/2) 3
    hH0 hb0 hH hb hLU (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end SymmetricSubgroupAsymptotics.NonaffineEightGeneratorSmallDegreeOrdinaryAggregate
