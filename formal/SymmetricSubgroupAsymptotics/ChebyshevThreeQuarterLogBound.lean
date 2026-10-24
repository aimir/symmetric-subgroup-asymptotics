import SymmetricSubgroupAsymptotics.TraceyElementarySharperLogBudget

/-! A uniform elementary improvement to the proved Chebyshev entropy
constant. The only numerical exp/log constants are existing Mathlib
proved rational bounds. There is no new analytic or published input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ChebyshevThreeQuarterLogBound

theorem log_le_three_quarters_sqrt (x : ℝ) (hx : 0 ≤ x) :
    Real.log x ≤ (3/4)*Real.sqrt x := by
  by_cases hz : x = 0
  · simpa only [hz,Real.log_zero,Real.sqrt_zero,mul_zero] using (le_rfl : (0 : ℝ) ≤ 0)
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
    have he : (8/3 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hconst : Real.log (8/3 : ℝ) ≤ 1 :=
      (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 8/3)).mpr he
    have hh := Real.log_le_sub_one_of_pos (div_pos hs (by norm_num : (0 : ℝ) < 8/3))
    rw [Real.log_div hs.ne' (by norm_num : (8/3 : ℝ) ≠ 0),Real.log_sqrt hx] at hh
    nlinarith only [hh,hconst]

theorem log_lcmUpto_le_seventeen_quarters_mul (v : ℕ) :
    Real.logb 2 (Nat.lcmUpto v : ℝ) ≤ (17/4)*(v : ℝ) := by
  by_cases hv : v = 0
  · subst v
    norm_num [Nat.lcmUpto]
  · have hvR : (1 : ℝ) ≤ v := by exact_mod_cast (show 1 ≤ v by omega)
    have hv0 : (0 : ℝ) ≤ v := by positivity
    rw [Real.logb,div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    rw [←Chebyshev.psi_eq_log_lcmUpto]
    have hp := Chebyshev.psi_le hvR
    have hlog := log_le_three_quarters_sqrt (v : ℝ) hv0
    have hterm := mul_le_mul_of_nonneg_left hlog
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg (v : ℝ)))
    have hsq := Real.sq_sqrt hv0
    have hlogtwo : (2 : ℝ)/3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlogterm := mul_le_mul_of_nonneg_right hlogtwo hv0
    have hfour : Real.log 4 = 2*Real.log 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num,Real.log_pow]
      norm_num
    rw [hfour] at hp
    nlinarith only [hp,hterm,hsq,hlogterm]

end SymmetricSubgroupAsymptotics.ChebyshevThreeQuarterLogBound
