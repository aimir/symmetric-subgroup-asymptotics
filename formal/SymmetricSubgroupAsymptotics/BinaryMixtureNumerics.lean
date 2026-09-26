import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The two numerical deficits used by the complete binary mixture.
These scalar inequalities keep physical half-degree, carrier weight and
group-order logarithm distinct. Counting, profile weights and error
absorption are supplied separately by their respective theorems.
-/
set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics.BinaryMixtureNumerics

/-- The carrier reserve loses a fixed multiple of carrier weight times
the total physical half-degree. -/
theorem carrier_reserve_le_linear (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T) :
    (R+4*T)^2/4 - (25/82)*R*T - (29/164)*T^2 ≤
      (R+4*T)^2/4 - (29/656)*T*(R+4*T) := by
  nlinarith [mul_nonneg hR hT]

/-- Increasing the critical rank enlarges the same carrier reserve. -/
theorem carrier_reserve_mono (R S T : ℝ) (hR : 0 ≤ R) (hRS : R ≤ S)
    (hT : 0 ≤ T) :
    (R+4*T)^2/4 - (25/82)*R*T - (29/164)*T^2 ≤
      (S+4*T)^2/4 - (25/82)*S*T - (29/164)*T^2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hRS) hT,
    mul_nonneg (sub_nonneg.mpr hRS) (add_nonneg hR (hR.trans hRS))]

/-- Exact lower bound for the Hall-mixture quadratic deficit when the
carrier order logarithm is at most one twentieth of the cyclic-four count. -/
theorem hall_deficit_lower (R a u : ℝ) (hR : 0 ≤ R) (ha : 0 ≤ a)
    (hu : 0 ≤ u) (hua : u ≤ a/20) :
    (19/40)*a*R + (17/160)*a^2 ≤
      a*R/2+a^2/6-u*R/2-(7/6)*a*u-(5/6)*u^2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hua) hR,
    mul_nonneg (sub_nonneg.mpr hua) ha,
    mul_nonneg (sub_nonneg.mpr hua) (show 0 ≤ a/20+u by positivity)]

/-- The small-carrier regime gives the stated deficit in the complete
physical half-degree R+2a+4T. No analytic error term is discarded here. -/
theorem hall_deficit_le_mixture (R a u T : ℝ) (hR : 0 ≤ R) (ha : 0 ≤ a)
    (hu : 0 ≤ u) (huT : u ≤ 7*T) (hTa : T ≤ a/140) :
    a*(R+2*a+4*T)/25 ≤
      a*R/2+a^2/6-u*R/2-(7/6)*a*u-(5/6)*u^2 := by
  have hua : u ≤ a/20 := by linarith
  have h := hall_deficit_lower R a u hR ha hu hua
  nlinarith [mul_nonneg ha hR, sq_nonneg a,
    mul_nonneg ha (sub_nonneg.mpr hTa)]

end SymmetricSubgroupAsymptotics.BinaryMixtureNumerics
