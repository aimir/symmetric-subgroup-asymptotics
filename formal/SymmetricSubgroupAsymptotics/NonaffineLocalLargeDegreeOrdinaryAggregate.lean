import SymmetricSubgroupAsymptotics.NonaffineLocalDegreeOrdinaryRealTail
import SymmetricSubgroupAsymptotics.ImprimitiveTopLogarithmicScaling
import SymmetricSubgroupAsymptotics.ActualWreathChiefUnitMinimumRate

/-! Uniform two-variable scalar fitting for actual local-socle costs.
The hypotheses concern genuine local degree, least index and outer-order
coefficients; no desired rank/capacity estimate is supplied. Every integer
top>=2 and its rounded coarse ceiling are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NonaffineLocalLargeDegreeOrdinaryAggregate
open ImprimitiveTopLogarithmicScaling ActualWreathChiefUnitMinimumRate

/-- The actual minimum rate has the same uniform logarithmic scaling. -/
theorem rate_mul_sqrt_log_add_le (L : ℝ) (hL : 0 ≤ L) (t : ℕ) (ht : 2 ≤ t) :
    rate t*Real.sqrt (L+Real.logb 2 (t : ℝ)) ≤ (t : ℝ)*Real.sqrt (L+1) := by
  let v := Real.sqrt (Real.logb 2 (t : ℝ))
  let w := Real.sqrt (L+Real.logb 2 (t : ℝ))
  let u := Real.sqrt (L+1)
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hv : 0 < v := Real.sqrt_pos.mpr
    (Real.logb_pos (by norm_num) (by linarith only [htR]))
  have hw : 0 ≤ w := Real.sqrt_nonneg _
  have hlog : w ≤ u*v := sqrt_log_add_le_mul_sqrt_log L hL t ht
  have hrate : rate t ≤ (t : ℝ)/v := min_le_right _ _
  calc
    rate t*w ≤ (t : ℝ)/v*w := mul_le_mul_of_nonneg_right hrate hw
    _ = (t : ℝ)*w/v := by ring
    _ ≤ ((t : ℝ)*(u*v))/v :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity)) hv.le
    _ = (t : ℝ)*u := by rw [←mul_assoc,mul_div_cancel_right₀ _ hv.ne']

/-- The square-root head and quadratic local quotient coefficient are paid
uniformly, with the ACTUAL rounded top ceiling included. -/
theorem square_root_cost_le (r t : ℕ) (hr : 1024 ≤ r) (ht : 2 ≤ t)
    (b : ℝ) (hb0 : 0 ≤ b)
    (hb : b ≤ (Real.logb 2 (r : ℝ))^2+5*Real.logb 2 (r : ℝ)) :
    2*Real.sqrt (r : ℝ)+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  let L := Real.logb 2 (r : ℝ)
  let e := Real.logb 2 (t : ℝ)
  let u := Real.sqrt (L+1)
  let w := Real.sqrt (L+e)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ r by omega))
  have he : 0 < e := Real.logb_pos (by norm_num) (by linarith only [htR])
  have hw : 0 < w := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hL he)
  have hhead := mul_le_mul_of_nonneg_left (sqrt_log_add_le_half_mul L hL t ht)
    (show 0 ≤ 2*Real.sqrt (r : ℝ) by positivity)
  have hrate := mul_le_mul_of_nonneg_left (rate_mul_sqrt_log_add_le L hL t ht) hb0
  have hcoeff := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ (t : ℝ)*u by positivity)
  have htop := ceiling_mul_sqrt_log_add_le L hL t ht
  have hscaled : (2*Real.sqrt (r : ℝ)+b*rate t+traceyPermutationGeneratorCeiling t)*w ≤
      (t : ℝ)*((Real.sqrt (r : ℝ)+L^2+5*L+3/2)*u) := by
    nlinarith only [hhead,hrate,hcoeff,htop]
  have htail := mul_le_mul_of_nonneg_left
    (NonaffineLocalDegreeOrdinaryRealTail.multiple_factor_budget r hr)
    (show (0 : ℝ) ≤ t by positivity)
  rw [Real.logb_mul hrR.ne' (by linarith only [htR] : (t : ℝ) ≠ 0)]
  change 2*Real.sqrt (r : ℝ)+b*rate t+traceyPermutationGeneratorCeiling t ≤ (r : ℝ)*(t : ℝ)/w
  apply (le_div_iff₀ hw).mpr
  nlinarith only [hscaled,htail]

/-- One local simple factor retains its ONE coset head. A large least index
relative to r is handled without assuming monotonicity of rounded ceilings. -/
theorem one_factor_cost_le (r t ell : ℕ) (hr : 1024 ≤ r) (ht : 2 ≤ t)
    (hell : 2 ≤ ell) (hellr : ell ≤ r) (hrpow : r ≤ ell^2)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 3+2*Real.logb 2 (r : ℝ)) :
    (traceyPermutationGeneratorCeiling ell : ℝ)+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  let L := Real.logb 2 (r : ℝ)
  let e := Real.logb 2 (t : ℝ)
  let l := Real.logb 2 (ell : ℝ)
  let u := Real.sqrt (L+1)
  let w := Real.sqrt (L+e)
  let v := Real.sqrt l
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hellrR : (ell : ℝ) ≤ r := by exact_mod_cast hellr
  have hL10 : 10 ≤ L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (2 : ℝ)^10)
      (show (2 : ℝ)^10 ≤ r by exact_mod_cast hr)
    simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] using hh
  have hL : 0 ≤ L := by linarith only [hL10]
  have he : 0 < e := Real.logb_pos (by norm_num) (by linarith only [htR])
  have hl : 0 < l := Real.logb_pos (by norm_num) (by linarith only [hellR])
  have hv : 0 < v := Real.sqrt_pos.mpr hl
  have hw : 0 < w := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hL he)
  have hLl : L ≤ 2*l := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hrR
      (show (r : ℝ) ≤ (ell : ℝ)^2 by exact_mod_cast hrpow)
    simpa only [Real.logb_pow] using hh
  have huv : u ≤ (3/2 : ℝ)*v := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    dsimp only [u,v]
    rw [mul_pow,Real.sq_sqrt (by linarith only [hL] : 0 ≤ L+1),Real.sq_sqrt hl.le]
    nlinarith only [hL10,hLl]
  have hceil : (traceyPermutationGeneratorCeiling ell : ℝ) ≤ (ell : ℝ)/v+1 := by
    change (⌈(ell : ℝ)/v⌉₊ : ℝ) ≤ (ell : ℝ)/v+1
    exact (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (ell : ℝ)/v by positivity)).le
  have hmain : (ell : ℝ)/v*u ≤ (3/2 : ℝ)*(r : ℝ) := by
    calc
      (ell : ℝ)/v*u = (ell : ℝ)*u/v := by ring
      _ ≤ ((ell : ℝ)*((3/2 : ℝ)*v))/v :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left huv (by positivity)) hv.le
      _ = (3/2 : ℝ)*(ell : ℝ) := by rw [←mul_assoc,mul_div_cancel_right₀ _ hv.ne']; ring
      _ ≤ (3/2 : ℝ)*(r : ℝ) := mul_le_mul_of_nonneg_left hellrR (by norm_num)
  have hheadu : (traceyPermutationGeneratorCeiling ell : ℝ)*u ≤ (3/2 : ℝ)*(r : ℝ)+u := by
    have hh := mul_le_mul_of_nonneg_right hceil (show 0 ≤ u by positivity)
    nlinarith only [hh,hmain]
  have hhead1 := mul_le_mul_of_nonneg_left (sqrt_log_add_le_half_mul L hL t ht)
    (show (0 : ℝ) ≤ traceyPermutationGeneratorCeiling ell by positivity)
  have hhead2 := mul_le_mul_of_nonneg_left hheadu (show 0 ≤ (t : ℝ)/2 by positivity)
  have hrate := mul_le_mul_of_nonneg_left (rate_mul_sqrt_log_add_le L hL t ht) hb0
  have hcoeff := mul_le_mul_of_nonneg_right hb (show 0 ≤ (t : ℝ)*u by positivity)
  have htop := ceiling_mul_sqrt_log_add_le L hL t ht
  have hscaled : ((traceyPermutationGeneratorCeiling ell : ℝ)+b*rate t+
      traceyPermutationGeneratorCeiling t)*w ≤
      (3/4 : ℝ)*(r : ℝ)*(t : ℝ)+(t : ℝ)*((2*L+5)*u) := by
    nlinarith only [hhead1,hhead2,hrate,hcoeff,htop]
  have htail := mul_le_mul_of_nonneg_left
    (NonaffineLocalDegreeOrdinaryRealTail.one_factor_outer_budget r hr)
    (show (0 : ℝ) ≤ t by positivity)
  rw [Real.logb_mul hrR.ne' (by linarith only [htR] : (t : ℝ) ≠ 0)]
  change (traceyPermutationGeneratorCeiling ell : ℝ)+b*rate t+traceyPermutationGeneratorCeiling t ≤
    (r : ℝ)*(t : ℝ)/w
  apply (le_div_iff₀ hw).mpr
  nlinarith only [hscaled,htail]

end SymmetricSubgroupAsymptotics.NonaffineLocalLargeDegreeOrdinaryAggregate
