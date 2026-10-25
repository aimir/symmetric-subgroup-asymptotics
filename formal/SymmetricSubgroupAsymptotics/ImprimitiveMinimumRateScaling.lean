import SymmetricSubgroupAsymptotics.ImprimitiveTopLogarithmicScaling
import SymmetricSubgroupAsymptotics.ActualWreathChiefUnitMinimumRate

/-! Sharper uniform scaling retains BOTH actual induced rates. The switch
is at log_2(t)=4, not at a chosen group or grid row. This is a scalar pilot;
no claim that an original source budget fits its final degree is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ImprimitiveMinimumRateScaling
open ImprimitiveTopLogarithmicScaling ActualWreathChiefUnitMinimumRate

/-- Half-rate increases up to the common switch and log-rate decreases
thereafter, giving one uniform bound for every integer top t>=2. -/
theorem rate_mul_sqrt_log_add_le (L : ℝ) (hL : 0 ≤ L) (t : ℕ) (ht : 2 ≤ t) :
    rate t*Real.sqrt (L+Real.logb 2 (t : ℝ)) ≤ (t : ℝ)/2*Real.sqrt (L+4) := by
  let e := Real.logb 2 (t : ℝ)
  let v := Real.sqrt e
  let w := Real.sqrt (L+e)
  let u := Real.sqrt (L+4)
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have he : 0 < e := Real.logb_pos (by norm_num) (by linarith only [htR])
  have hv : 0 < v := Real.sqrt_pos.mpr he
  have hw : 0 ≤ w := Real.sqrt_nonneg _
  by_cases hs : e ≤ 4
  · have hwu : w ≤ u := Real.sqrt_le_sqrt (add_le_add (le_refl L) hs)
    have hrate : rate t ≤ (t : ℝ)/2 := min_le_left _ _
    exact (mul_le_mul_of_nonneg_right hrate hw).trans
      (mul_le_mul_of_nonneg_left hwu (by positivity))
  · have he4 : 4 ≤ e := le_of_not_ge hs
    have hsq : (2*w)^2 ≤ (u*v)^2 := by
      dsimp only [w,u,v]
      rw [mul_pow,mul_pow,Real.sq_sqrt (add_nonneg hL he.le),
        Real.sq_sqrt (by linarith only [hL] : 0 ≤ L+4),Real.sq_sqrt he.le]
      norm_num only [show (2 : ℝ)^2 = 4 by norm_num]
      nlinarith only [mul_nonneg hL (show 0 ≤ e-4 by linarith only [he4])]
    have hprod : 2*w ≤ u*v :=
      (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
    have hwu : w ≤ u*v/2 := by linarith only [hprod]
    have hrate : rate t ≤ (t : ℝ)/v := min_le_right _ _
    calc
      rate t*w ≤ (t : ℝ)/v*w := mul_le_mul_of_nonneg_right hrate hw
      _ = (t : ℝ)*w/v := by ring
      _ ≤ ((t : ℝ)*(u*v/2))/v :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwu (by positivity)) hv.le
      _ = (t : ℝ)/2*u := by
        calc
          ((t : ℝ)*(u*v/2))/v = (((t : ℝ)/2*u)*v)/v := by ring
          _ = (t : ℝ)/2*u := mul_div_cancel_right₀ _ hv.ne'

/-- Rounding the actual top ceiling costs at most twice the same minimum
rate; this preserves the half-rate regime at small top degrees. -/
theorem ceiling_le_twice_rate (t : ℕ) (ht : 2 ≤ t) :
    (traceyPermutationGeneratorCeiling t : ℝ) ≤ 2*rate t := by
  let e := Real.logb 2 (t : ℝ)
  let v := Real.sqrt e
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have he : 1 ≤ e := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) htR
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hh
  have hv : 0 < v := Real.sqrt_pos.mpr (by linarith only [he])
  have hv1 : 1 ≤ v := by
    have hh := Real.sqrt_le_sqrt he
    simpa only [Real.sqrt_one] using hh
  by_cases hh : (t : ℝ)/2 ≤ (t : ℝ)/v
  · have hnat : traceyPermutationGeneratorCeiling t ≤ t := by
      apply Nat.ceil_le.mpr
      apply (div_le_iff₀ hv).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hv1 (show (0 : ℝ) ≤ t by positivity)]
    have hreal : (traceyPermutationGeneratorCeiling t : ℝ) ≤ t := by exact_mod_cast hnat
    rw [rate,min_eq_left hh]
    linarith only [hreal]
  · have hmin : rate t = (t : ℝ)/v := min_eq_right (le_of_not_ge hh)
    have hr := one_le_rate t ht
    rw [hmin] at hr
    have hceil : (traceyPermutationGeneratorCeiling t : ℝ) ≤ (t : ℝ)/v+1 := by
      change (⌈(t : ℝ)/v⌉₊ : ℝ) ≤ (t : ℝ)/v+1
      exact (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (t : ℝ)/v by positivity)).le
    rw [hmin]
    linarith only [hr,hceil]

/-- A displayed-pair head is kept separate from the actual quotient
coefficient and the actual rounded top ceiling. No final fit is assumed. -/
theorem displayed_pair_cost_scaled (L b : ℝ) (hL : 0 ≤ L) (hb : 0 ≤ b)
    (t : ℕ) (ht : 2 ≤ t) :
    (2+b*rate t+traceyPermutationGeneratorCeiling t)*Real.sqrt (L+Real.logb 2 (t : ℝ)) ≤
      (t : ℝ)*(Real.sqrt (L+1)+(b+2)/2*Real.sqrt (L+4)) := by
  have htop := ceiling_le_twice_rate t ht
  have hhead := sqrt_log_add_le_half_mul L hL t ht
  have hrate := mul_le_mul_of_nonneg_left (rate_mul_sqrt_log_add_le L hL t ht)
    (show 0 ≤ b+2 by linarith only [hb])
  have hsource := mul_le_mul_of_nonneg_right htop
    (Real.sqrt_nonneg (L+Real.logb 2 (t : ℝ)))
  nlinarith only [hsource,hhead,hrate]

end SymmetricSubgroupAsymptotics.ImprimitiveMinimumRateScaling
