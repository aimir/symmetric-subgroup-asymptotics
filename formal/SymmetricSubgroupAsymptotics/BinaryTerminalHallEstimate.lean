import SymmetricSubgroupAsymptotics.TerminalEstimates

/-!
# A terminal estimate with the Hall quadratic coefficient

The complete relation-dimension sum is retained. A bound on its inflation
dimension gives the quadratic loss (b+7)^2/3, with only the explicit finite
sum lengths outside the exponential. This is a scalar theorem; it assumes
no subgroup-count or profile-coverage conclusion.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- Completing the square retains the coefficient needed in the Hall
mixture deficit. The inequality itself holds for all real parameters. -/
theorem terminalHall_quadratic_le (b l : ℝ) :
    (b+7)*l - 3*l^2/4 ≤ (b+7)^2/3 := by
  nlinarith [sq_nonneg (3*l-2*(b+7))]

/-- Drop only the nonnegative terminal deficit, and bound the original
72^l factor by 2^(7l). No restriction on the relation index is needed. -/
theorem terminalRelationWeight_le_hall (r c d τ b l : ℕ)
    (hc : 2*c ≤ r) (hτ : τ ≤ b) :
    terminalRelationWeight r c d τ l ≤ (2 : ℝ)^(((b : ℝ)+7)^2/3) := by
  have hc' : 2*(c : ℝ) ≤ r := by exact_mod_cast hc
  have hτ' : (τ : ℝ) ≤ b := by exact_mod_cast hτ
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hgap : 0 ≤ (r : ℝ)/2-c+d/2 := by linarith
  have h72 : (72 : ℝ)^l ≤ (2 : ℝ)^(7*(l : ℝ)) := by
    calc
      _ ≤ ((2 : ℝ)^(7 : ℕ))^l :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) l
      _ = _ := by rw [← pow_mul, ← Real.rpow_natCast]; push_cast; rfl
  unfold terminalRelationWeight
  calc
    _ ≤ (2 : ℝ)^(7*(l : ℝ)) *
        (2 : ℝ)^(-((l : ℝ)*((r : ℝ)/2-c+d/2-τ))-3*(l : ℝ)^2/4) :=
      mul_le_mul_of_nonneg_right h72 (by positivity)
    _ = (2 : ℝ)^(7*(l : ℝ)-
        (l : ℝ)*((r : ℝ)/2-c+d/2-τ)-3*(l : ℝ)^2/4) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ (2 : ℝ)^(((b : ℝ)+7)*(l : ℝ)-3*(l : ℝ)^2/4) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_nonneg hl hgap, mul_nonneg hl (sub_nonneg.mpr hτ')]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (terminalHall_quadratic_le (b : ℝ) (l : ℝ))

/-- A uniform complete terminal sum bound with the exact quadratic
coefficient 1/3 and both finite summation lengths explicit. -/
theorem terminalGaussianDoubleSum_hall_le (r c d τ b : ℕ)
    (hc : 2*c ≤ r) (hτ : τ ≤ b) :
    terminalGaussianDoubleSum r c d τ ≤
      2 * (eulerProduct⁻¹)^3 * (r+1) * (c+1) * terminalGaussianWeight r d *
        (2 : ℝ)^(((b : ℝ)+7)^2/3) := by
  have hsum : (∑ l ∈ Finset.range (c+1), terminalRelationWeight r c d τ l) ≤
      ((c : ℝ)+1) * (2 : ℝ)^(((b : ℝ)+7)^2/3) := by
    calc
      _ ≤ ∑ _l ∈ Finset.range (c+1), (2 : ℝ)^(((b : ℝ)+7)^2/3) := by
        apply Finset.sum_le_sum
        intro l _
        exact terminalRelationWeight_le_hall r c d τ b l hc hτ
      _ = _ := by simp
  calc
    _ ≤ 2 * (eulerProduct⁻¹)^3 * (r+1) * terminalGaussianWeight r d *
        ∑ l ∈ Finset.range (c+1), terminalRelationWeight r c d τ l :=
      terminalGaussianDoubleSum_le r c d τ
    _ ≤ 2 * (eulerProduct⁻¹)^3 * (r+1) * terminalGaussianWeight r d *
        (((c : ℝ)+1) * (2 : ℝ)^(((b : ℝ)+7)^2/3)) :=
      mul_le_mul_of_nonneg_left hsum (by
        have hw := (terminalGaussianWeight_pos r d).le
        positivity [euler_positive])
    _ = _ := by ring

end SymmetricSubgroupAsymptotics
