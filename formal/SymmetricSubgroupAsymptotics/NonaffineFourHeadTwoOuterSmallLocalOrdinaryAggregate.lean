import SymmetricSubgroupAsymptotics.NonaffineBoundedHeadSmallLocalOrdinaryAggregate

/-! Four actual head generators and at most two outer prime factors pay
every inherited top in local degrees14..31. This scalar statement has
no group, model, or fitted aggregate premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NonaffineFourHeadTwoOuterSmallLocalOrdinaryAggregate
open ActualWreathChiefUnitMinimumRate

theorem cost_le (r t : ℕ) (hr : 14 ≤ r) (hsmall : r < 32) (ht : 2 ≤ t)
    (H b : ℝ) (hH0 : 0 ≤ H) (hH : H ≤ 4) (hb0 : 0 ≤ b) (hb : b ≤ 2) :
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
  have hLU : L ≤ 5 := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 5 (by omega) (by decide)
      (by simpa only [pow_one] using (show r ≤ 2^5 by omega))
    simpa only [Nat.cast_one,div_one] using hh
  have he : 0 < e := Real.logb_pos (by norm_num) (by linarith only [htR])
  have hw : 0 < w := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hL he)
  have hroot1 : u1 ≤ (5/2 : ℝ) := Real.sqrt_le_iff.mpr
    ⟨by norm_num,by linarith only [hLU]⟩
  have hroot4 : u4 ≤ 3 := Real.sqrt_le_iff.mpr
    ⟨by norm_num,by linarith only [hLU]⟩
  have hh1 := mul_le_mul hH hroot1 (Real.sqrt_nonneg (L+1)) (by norm_num : (0:ℝ) ≤ 4)
  have hh4 := mul_le_mul (show b+2 ≤ 4 by linarith only [hb]) hroot4
    (Real.sqrt_nonneg (L+4)) (by norm_num : (0:ℝ) ≤ 4)
  have hr14 : (14:ℝ) ≤ r := by exact_mod_cast hr
  have hmargin : H/2*u1+(b+2)/2*u4 ≤ (r : ℝ) := by
    nlinarith only [hh1,hh4,hr14]
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

end SymmetricSubgroupAsymptotics.NonaffineFourHeadTwoOuterSmallLocalOrdinaryAggregate
