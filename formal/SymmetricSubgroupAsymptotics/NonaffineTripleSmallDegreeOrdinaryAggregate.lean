import SymmetricSubgroupAsymptotics.NonaffineTinyPairLargeTopOrdinaryAggregate
import SymmetricSubgroupAsymptotics.ImprimitiveMinimumRateScaling

/-! A uniform small-component estimate for a three-generator simple
head and at most five outer prime factors. Every inherited top degree
is retained. The proof uses two top ranges, not action-specific rows. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NonaffineTripleSmallDegreeOrdinaryAggregate
open ActualWreathChiefUnitMinimumRate

theorem cost_le (r t : ℕ) (hr : 20 ≤ r) (hsmall : r ≤ 31)
    (ht : 2 ≤ t) (b : ℝ) (hb : b ≤ 5) :
    3+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  let L := Real.logb 2 (r : ℝ)
  let e := Real.logb 2 (t : ℝ)
  let v := Real.sqrt e
  let w := Real.sqrt (L+e)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hr20 : (20 : ℝ) ≤ r := by exact_mod_cast hr
  have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) (by linarith only [hr20])
  have hL5 : L ≤ 5 := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 5 (by omega) (by decide)
      (by simpa only [pow_one] using (show r ≤ 2^5 by omega))
    simpa only [Nat.cast_one,div_one] using hh
  have he : 0 < e := Real.logb_pos (by norm_num) (by linarith only [ht2])
  have hv : 0 < v := Real.sqrt_pos.mpr he
  have hw : 0 < w := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hL0 he)
  have hratenonneg : 0 ≤ rate t := (one_le_rate t ht).trans' (by norm_num)
  have hbRate := mul_le_mul_of_nonneg_right hb hratenonneg
  have hscaled : (3+b*rate t+traceyPermutationGeneratorCeiling t)*w ≤ (r : ℝ)*(t : ℝ) := by
    by_cases hlarge : 4 ≤ t
    · have he2 : 2 ≤ e := by
        have hh := IntegerLogSquareRootCeilingCertificate.log_lower t 1 2 (by omega) (by decide)
          (by simpa only [pow_one] using hlarge)
        simpa only [Nat.cast_one,div_one] using hh
      have hwv : w ≤ 2*v := by
        apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
        dsimp only [w,v]
        rw [mul_pow,Real.sq_sqrt (add_nonneg hL0 he.le),Real.sq_sqrt he.le]
        nlinarith only [hL5,he2]
      have hcost : 3+b*rate t+traceyPermutationGeneratorCeiling t ≤ 10*rate t := by
        have htop := ImprimitiveMinimumRateScaling.ceiling_le_twice_rate t ht
        have hone := one_le_rate t ht
        nlinarith only [hbRate,htop,hone]
      have hrate : rate t ≤ (t : ℝ)/v := min_le_right _ _
      have hbound : 3+b*rate t+traceyPermutationGeneratorCeiling t ≤ 10*((t : ℝ)/v) :=
        hcost.trans (mul_le_mul_of_nonneg_left hrate (by norm_num))
      calc
        (3+b*rate t+traceyPermutationGeneratorCeiling t)*w ≤ 10*((t : ℝ)/v)*w :=
          mul_le_mul_of_nonneg_right hbound hw.le
        _ ≤ 10*((t : ℝ)/v)*(2*v) :=
          mul_le_mul_of_nonneg_left hwv (by positivity)
        _ = 20*(t : ℝ) := by field_simp; ring
        _ ≤ (r : ℝ)*(t : ℝ) := mul_le_mul_of_nonneg_right hr20 ht0.le
    · have he2 : e ≤ 2 := by
        have hh := IntegerLogSquareRootCeilingCertificate.log_upper t 1 2 (by omega) (by decide)
          (by simpa only [pow_one] using (show t ≤ 2^2 by omega))
        simpa only [Nat.cast_one,div_one] using hh
      have hw3 : w ≤ 3 := Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith only [hL5,he2]⟩
      have hrate : rate t ≤ (t : ℝ)/2 := min_le_left _ _
      have htop : (traceyPermutationGeneratorCeiling t : ℝ) ≤ t := by
        have hh := ImprimitiveMinimumRateScaling.ceiling_le_twice_rate t ht
        linarith only [hh,hrate]
      have hcost : 3+b*rate t+traceyPermutationGeneratorCeiling t ≤ 3+7*(t : ℝ)/2 := by
        linarith only [hbRate,hrate,htop]
      calc
        (3+b*rate t+traceyPermutationGeneratorCeiling t)*w ≤ (3+7*(t : ℝ)/2)*w :=
          mul_le_mul_of_nonneg_right hcost hw.le
        _ ≤ (3+7*(t : ℝ)/2)*3 := mul_le_mul_of_nonneg_left hw3 (by positivity)
        _ ≤ 20*(t : ℝ) := by linarith only [ht2]
        _ ≤ (r : ℝ)*(t : ℝ) := mul_le_mul_of_nonneg_right hr20 ht0.le
  rw [Real.logb_mul hr0.ne' ht0.ne']
  change 3+b*rate t+traceyPermutationGeneratorCeiling t ≤ (r : ℝ)*(t : ℝ)/w
  exact (le_div_iff₀ hw).mpr hscaled

end SymmetricSubgroupAsymptotics.NonaffineTripleSmallDegreeOrdinaryAggregate
