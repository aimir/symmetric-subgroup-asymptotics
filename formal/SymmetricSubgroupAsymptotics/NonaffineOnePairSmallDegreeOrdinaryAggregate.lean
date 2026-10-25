import SymmetricSubgroupAsymptotics.ImprimitiveMinimumRateScaling
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! One actual pair head, outer multiplicity at most three and the
rounded actual top ceiling fit all local degrees from 10 through 24.
This is one scalar band, not a list of actions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NonaffineOnePairSmallDegreeOrdinaryAggregate
open ActualWreathChiefUnitMinimumRate

theorem one_pair_cost_le (r t : ℕ) (hr : 10 ≤ r) (hsmall : r < 25) (ht : 2 ≤ t)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 3) :
    2+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  let L := Real.logb 2 (r : ℝ)
  let e := Real.logb 2 (t : ℝ)
  let w := Real.sqrt (L+e)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (show 1 ≤ r by omega))
  have he : 0 < e := Real.logb_pos (by norm_num) (by linarith only [htR])
  have hw : 0 < w := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hL he)
  have hLu : L ≤ 5 := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 5
      (by omega) (by decide) (by simpa only [pow_one] using (show r ≤ 2^5 by omega))
    simpa only [Nat.cast_one,div_one] using hh
  have hroot1 : Real.sqrt (L+1) ≤ 5/2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith only [hLu]⟩
  have hroot4 : Real.sqrt (L+4) ≤ 3 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith only [hLu]⟩
  have hcoeff : (b+2)/2 ≤ 5/2 := by linarith only [hb]
  have hprod := mul_le_mul hcoeff hroot4 (Real.sqrt_nonneg (L+4))
    (by norm_num : (0 : ℝ) ≤ 5/2)
  have hmargin : Real.sqrt (L+1)+(b+2)/2*Real.sqrt (L+4) ≤ (r : ℝ) := by
    have hr10 : (10 : ℝ) ≤ r := by exact_mod_cast hr
    linarith only [hroot1,hprod,hr10]
  have hscaled := ImprimitiveMinimumRateScaling.displayed_pair_cost_scaled L b hL hb0 t ht
  have hlast := mul_le_mul_of_nonneg_left hmargin (show (0 : ℝ) ≤ t by positivity)
  rw [Real.logb_mul hrR.ne' (by linarith only [htR] : (t : ℝ) ≠ 0)]
  change 2+b*rate t+traceyPermutationGeneratorCeiling t ≤ (r : ℝ)*(t : ℝ)/w
  apply (le_div_iff₀ hw).mpr
  nlinarith only [hscaled,hlast]

end SymmetricSubgroupAsymptotics.NonaffineOnePairSmallDegreeOrdinaryAggregate
