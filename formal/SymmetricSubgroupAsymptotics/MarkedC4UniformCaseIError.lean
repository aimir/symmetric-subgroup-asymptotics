import SymmetricSubgroupAsymptotics.MarkedC4ActualUniformOriginalCaseI
import SymmetricSubgroupAsymptotics.MarkedC4ErrorCalculus

/-! The physical stopping cost of the actual Case-I theorem is negligible.
This cost is charged at the stopping leaf, not at every excessive peel.
The ONE global marking polynomial is handled separately by SingleMarkError. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MarkedC4.UniformCaseIError
open ActualUniformOriginalCaseI

def coefficient (C : ℕ) : ℝ := 1+2^(2^C)+(C : ℝ)^2+3*C+2

theorem coefficient_nonneg (C : ℕ) : 0 ≤ coefficient C := by
  unfold coefficient
  positivity

theorem costExponent_le {b : ℕ} (hb : 1 ≤ b) (C : ℕ) :
    costExponent C b ≤ coefficient C*b := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hm := mul_le_mul_of_nonneg_left hb1 (show 0 ≤ (3 : ℝ)*C+2 by positivity)
  unfold costExponent coefficient
  push_cast
  nlinarith

/-- An explicit O_C(b log(b+r+2)) envelope for the actual physical cost. -/
theorem physical_cost_le_error {b : ℕ} (hb : 1 ≤ b) (C r : ℕ) :
    ((b : ℝ)+2)^costExponent C b ≤
      (2 : ℝ)^(boundedWordError (coefficient C) b r) := by
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log ((b : ℝ)+2) ≤ Real.log ((b : ℝ)+r+2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hl0 : 0 ≤ Real.log ((b : ℝ)+r+2) := Real.log_nonneg (by linarith)
  have hc := coefficient_nonneg C
  have hcost0 : 0 ≤ costExponent C b := by unfold costExponent; positivity
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2) (by positivity)).mp
  rw [Real.logb,Real.log_rpow (by positivity)]
  apply (div_le_iff₀ hd).mpr
  have hfirst := mul_le_mul_of_nonneg_left hl hcost0
  have hsecond := mul_le_mul_of_nonneg_right (costExponent_le hb C) hl0
  have hthird := mul_le_mul_of_nonneg_right
    (show coefficient C*(b : ℝ) ≤ (coefficient C+1)*b by nlinarith) hl0
  unfold boundedWordError
  field_simp
  nlinarith

theorem error_negligible (C : ℕ) :
    UniformQuadraticNegligible (boundedWordError (coefficient C)) :=
  boundedWordError_negligible (coefficient_nonneg C)

end SymmetricSubgroupAsymptotics.MarkedC4.UniformCaseIError
end
