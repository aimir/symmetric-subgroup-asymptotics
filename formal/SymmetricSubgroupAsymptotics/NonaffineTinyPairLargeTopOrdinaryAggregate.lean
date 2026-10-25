import SymmetricSubgroupAsymptotics.NonaffineOnePairSmallDegreeOrdinaryAggregate
import SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeSwitchNumerics

/-! Uniform large-top bounds for the two genuinely tiny pair bands.
The logarithmic quotient rate, actual ceiling error and fixed pair head
are treated jointly; no action rows or endpoint fit clauses are inputs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NonaffineTinyPairLargeTopOrdinaryAggregate
open ActualWreathChiefUnitMinimumRate

private theorem cost_bound (r t : ℕ) (hr : 1 ≤ r) (ht : 16 ≤ t)
    (b c z U : ℝ) (hb : b+1 ≤ c) (hc : 1 ≤ c) (hz : c ≤ z)
    (hU : U ≤ 4) (hL : Real.logb 2 (r : ℝ) ≤ U)
    (hcoef : c^2*U ≤ 4*(z^2-c^2)) (hdegree : z+1 ≤ (r : ℝ)) :
    2+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  let L := Real.logb 2 (r : ℝ)
  let e := Real.logb 2 (t : ℝ)
  let v := Real.sqrt e
  let w := Real.sqrt (L+e)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have htR : (16 : ℝ) ≤ t := by exact_mod_cast ht
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) (by exact_mod_cast hr)
  have he4 : 4 ≤ e := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_lower t 1 4 (by omega) (by decide)
      (by simpa only [pow_one] using ht)
    simpa only [Nat.cast_one,div_one] using hh
  have he : 0 < e := by linarith only [he4]
  have hv : 0 < v := Real.sqrt_pos.mpr he
  have hw : 0 < w := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hL0 he)
  have hc0 : 0 ≤ c := by linarith only [hc]
  have hz0 : 0 ≤ z := hc0.trans hz
  have hzsq : 0 ≤ z^2-c^2 := sub_nonneg.mpr ((sq_le_sq₀ hc0 hz0).mpr hz)
  have hmainSq : (c*w)^2 ≤ (z*v)^2 := by
    dsimp only [w,v]
    rw [mul_pow,mul_pow,Real.sq_sqrt (add_nonneg hL0 he.le),Real.sq_sqrt he.le]
    have hh1 := mul_le_mul_of_nonneg_left hL (sq_nonneg c)
    have hh2 := mul_le_mul_of_nonneg_left he4 hzsq
    nlinarith only [hh1,hh2,hcoef]
  have hmain : c*w ≤ z*v := (sq_le_sq₀ (by positivity) (by positivity)).mp hmainSq
  have heUpper : e ≤ (t : ℝ)-1 :=
    BinaryAffineDominantPrimeSwitchNumerics.logb_nat_le_sub_one t (by omega)
  have herrorSq : (3*w)^2 ≤ (t : ℝ)^2 := by
    dsimp only [w]
    rw [mul_pow,Real.sq_sqrt (add_nonneg hL0 he.le)]
    nlinarith only [hL,hU,heUpper,htR,sq_nonneg ((t : ℝ)-16)]
  have herror : 3*w ≤ (t : ℝ) :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp herrorSq
  have htop : (traceyPermutationGeneratorCeiling t : ℝ) ≤ (t : ℝ)/v+1 := by
    change (⌈(t : ℝ)/v⌉₊ : ℝ) ≤ (t : ℝ)/v+1
    exact (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (t : ℝ)/v)).le
  have hrate : rate t ≤ (t : ℝ)/v := min_le_right _ _
  have hratenonneg : 0 ≤ rate t := (one_le_rate t (by omega)).trans' (by norm_num)
  have hcost : 2+b*rate t+traceyPermutationGeneratorCeiling t ≤ c*(t : ℝ)/v+3 := by
    have hh := mul_le_mul_of_nonneg_right hb hratenonneg
    have hh' := mul_le_mul_of_nonneg_left hrate (show 0 ≤ c-1 by linarith only [hc])
    have hfinal : 2+b*rate t+traceyPermutationGeneratorCeiling t ≤ c*((t : ℝ)/v)+3 := by
      nlinarith only [htop,hh,hh']
    simpa only [mul_div_assoc] using hfinal
  have hscaled : (2+b*rate t+traceyPermutationGeneratorCeiling t)*w ≤ (r : ℝ)*(t : ℝ) := by
    calc
      (2+b*rate t+traceyPermutationGeneratorCeiling t)*w ≤ (c*(t : ℝ)/v+3)*w :=
        mul_le_mul_of_nonneg_right hcost hw.le
      _ = (t : ℝ)*(c*w)/v+3*w := by ring
      _ ≤ (t : ℝ)*(z*v)/v+(t : ℝ) := add_le_add
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmain (by positivity)) hv.le) herror
      _ = (z+1)*(t : ℝ) := by rw [←mul_assoc,mul_div_cancel_right₀ _ hv.ne']; ring
      _ ≤ (r : ℝ)*(t : ℝ) := mul_le_mul_of_nonneg_right hdegree (by positivity)
  rw [Real.logb_mul hrR.ne' (by linarith only [htR] : (t : ℝ) ≠ 0)]
  change 2+b*rate t+traceyPermutationGeneratorCeiling t ≤ (r : ℝ)*(t : ℝ)/w
  exact (le_div_iff₀ hw).mpr hscaled

theorem five_six_cost_le (r t : ℕ) (hr : 5 ≤ r) (hr6 : r ≤ 6) (ht : 16 ≤ t)
    (b : ℝ) (hb : b ≤ 2) :
    2+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  have hL : Real.logb 2 (r : ℝ) ≤ 3 := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 3 (by omega) (by decide)
      (by simpa only [pow_one] using (show r ≤ 2^3 by omega))
    simpa only [Nat.cast_one,div_one] using hh
  exact cost_bound r t (by omega) ht b 3 4 3 (by linarith only [hb]) (by norm_num)
    (by norm_num) (by norm_num) hL (by norm_num) (by exact_mod_cast hr)

theorem seven_nine_cost_le (r t : ℕ) (hr : 7 ≤ r) (hr9 : r ≤ 9) (ht : 16 ≤ t)
    (b : ℝ) (hb : b ≤ 3) :
    2+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  have hL : Real.logb 2 (r : ℝ) ≤ 4 := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 4 (by omega) (by decide)
      (by simpa only [pow_one] using (show r ≤ 2^4 by omega))
    simpa only [Nat.cast_one,div_one] using hh
  exact cost_bound r t (by omega) ht b 4 6 4 (by linarith only [hb]) (by norm_num)
    (by norm_num) (by norm_num) hL (by norm_num) (by exact_mod_cast hr)

end SymmetricSubgroupAsymptotics.NonaffineTinyPairLargeTopOrdinaryAggregate
