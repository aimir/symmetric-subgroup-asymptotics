import SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeSwitchNumerics
import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput

/-! Uniform top-degree scaling for an imprimitive ordinary-generator
recurrence. The original top count is an arbitrary integer t>=2; no grid,
prime-power shape or fitted aggregate is assumed. These comparisons reduce
two-variable source costs to a scalar bound in the genuine local degree. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ImprimitiveTopLogarithmicScaling

/-- Integer log control gives a uniform square comparison at every top. -/
theorem four_log_add_le_square_mul (L : ℝ) (hL : 0 ≤ L) (t : ℕ) (ht : 2 ≤ t) :
    4*(L+Real.logb 2 (t : ℝ)) ≤ (t : ℝ)^2*(L+1) := by
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hlog := BinaryAffineDominantPrimeSwitchNumerics.logb_nat_le_sub_one t ht
  have hlog4 : 4*Real.logb 2 (t : ℝ) ≤ (t : ℝ)^2 := by
    nlinarith only [hlog,sq_nonneg ((t : ℝ)-2)]
  have hs : 0 ≤ (t : ℝ)^2-4 := by
    nlinarith only [htR,sq_nonneg ((t : ℝ)-2)]
  nlinarith only [hlog4,mul_nonneg hL hs]

/-- The normalized head charge is largest at the smallest integer top. -/
theorem sqrt_log_add_le_half_mul (L : ℝ) (hL : 0 ≤ L) (t : ℕ) (ht : 2 ≤ t) :
    Real.sqrt (L+Real.logb 2 (t : ℝ)) ≤ (t : ℝ)/2*Real.sqrt (L+1) := by
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have he : 0 ≤ Real.logb 2 (t : ℝ) :=
    Real.logb_nonneg (by norm_num) (by linarith only [htR])
  have hh := four_log_add_le_square_mul L hL t ht
  have hs : (2*Real.sqrt (L+Real.logb 2 (t : ℝ)))^2 ≤
      ((t : ℝ)*Real.sqrt (L+1))^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (add_nonneg hL he),
      Real.sq_sqrt (by linarith only [hL] : 0 ≤ L+1)]
    simpa only [show (2 : ℝ)^2 = 4 by norm_num] using hh
  have hc := (sq_le_sq₀ (by positivity : 0 ≤ 2*Real.sqrt (L+Real.logb 2 (t : ℝ)))
    (by positivity : 0 ≤ (t : ℝ)*Real.sqrt (L+1))).mp hs
  nlinarith only [hc]

/-- The log-rate charge scales by at most sqrt(L+1), uniformly in t. -/
theorem sqrt_log_add_le_mul_sqrt_log (L : ℝ) (hL : 0 ≤ L) (t : ℕ) (ht : 2 ≤ t) :
    Real.sqrt (L+Real.logb 2 (t : ℝ)) ≤
      Real.sqrt (L+1)*Real.sqrt (Real.logb 2 (t : ℝ)) := by
  have he : 1 ≤ Real.logb 2 (t : ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ t by exact_mod_cast ht)
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hh
  have hh : L+Real.logb 2 (t : ℝ) ≤ (L+1)*Real.logb 2 (t : ℝ) := by
    nlinarith only [mul_nonneg hL (show 0 ≤ Real.logb 2 (t : ℝ)-1 by linarith only [he])]
  have hs : (Real.sqrt (L+Real.logb 2 (t : ℝ)))^2 ≤
      (Real.sqrt (L+1)*Real.sqrt (Real.logb 2 (t : ℝ)))^2 := by
    rw [mul_pow,Real.sq_sqrt (by linarith only [hL,he] : 0 ≤ L+Real.logb 2 (t : ℝ)),
      Real.sq_sqrt (by linarith only [hL] : 0 ≤ L+1),Real.sq_sqrt (by linarith only [he])]
    exact hh
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp hs

/-- The ACTUAL rounded top ceiling, including its error, has a single
uniform scaled bound. The top bound itself is supplied by smaller action
induction in a separate original-source installer. -/
theorem ceiling_mul_sqrt_log_add_le (L : ℝ) (hL : 0 ≤ L) (t : ℕ) (ht : 2 ≤ t) :
    (traceyPermutationGeneratorCeiling t : ℝ)*Real.sqrt (L+Real.logb 2 (t : ℝ)) ≤
      (3/2 : ℝ)*(t : ℝ)*Real.sqrt (L+1) := by
  let v := Real.sqrt (Real.logb 2 (t : ℝ))
  let w := Real.sqrt (L+Real.logb 2 (t : ℝ))
  let u := Real.sqrt (L+1)
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hv : 0 < v := Real.sqrt_pos.mpr
    (Real.logb_pos (by norm_num) (by linarith only [htR]))
  have hw : 0 ≤ w := Real.sqrt_nonneg _
  have hceil : (traceyPermutationGeneratorCeiling t : ℝ) ≤ (t : ℝ)/v+1 := by
    change (⌈(t : ℝ)/v⌉₊ : ℝ) ≤ (t : ℝ)/v+1
    exact (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (t : ℝ)/v by positivity)).le
  have hhead : w ≤ (t : ℝ)/2*u := sqrt_log_add_le_half_mul L hL t ht
  have hlog : w ≤ u*v := sqrt_log_add_le_mul_sqrt_log L hL t ht
  have hmain : (t : ℝ)/v*w ≤ (t : ℝ)*u := by
    calc
      (t : ℝ)/v*w = (t : ℝ)*w/v := by ring
      _ ≤ ((t : ℝ)*(u*v))/v :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity)) hv.le
      _ = (t : ℝ)*u := by rw [←mul_assoc,mul_div_cancel_right₀ _ hv.ne']
  have hh := mul_le_mul_of_nonneg_right hceil hw
  change (traceyPermutationGeneratorCeiling t : ℝ)*w ≤ (3/2 : ℝ)*(t : ℝ)*u
  nlinarith only [hh,hmain,hhead]

end SymmetricSubgroupAsymptotics.ImprimitiveTopLogarithmicScaling
