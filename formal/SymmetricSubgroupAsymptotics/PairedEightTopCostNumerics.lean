import SymmetricSubgroupAsymptotics.TernaryOddPartTopAnchorEnvelope
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! A common cold exponent for the three independent top-cost branches. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.PairedEightTopCostNumerics

theorem ordinary_le : Real.logb 2 5/3 ≤ (7/9 : ℝ) := by
  have hp : (5 : ℝ)^3 ≤ (2 : ℝ)^7 := by norm_num
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (pow_pos (by norm_num : (0 : ℝ)<5) 3) hp
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),
    mul_one] at h
  norm_num at h
  linarith

theorem relative_le : Real.logb 2 (38/25) ≤ (5/8 : ℝ) := by
  have hp : ((38/25 : ℝ)^8) ≤ (2 : ℝ)^5 := by norm_num
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (pow_pos (by norm_num : (0 : ℝ)<38/25) 8) hp
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),
    mul_one] at h
  norm_num at h
  linarith

theorem binary_plus_two_cold :
    2*Real.logb 2 (38/25)+(51/200 : ℝ)*2 ≤ 31/16 := by
  linarith [relative_le]

theorem anchor_plus_two_cold :
    Real.logb 2 5/3+Real.logb 2 (38/25)+(51/200 : ℝ)*2 ≤ 31/16 := by
  linarith [ordinary_le,relative_le]

theorem general_two_plus_one_cold :
    2*(Real.logb 2 5/3)+(51/200 : ℝ)*1 ≤ 31/16 := by
  linarith [ordinary_le]

end SymmetricSubgroupAsymptotics.PairedEightTopCostNumerics
