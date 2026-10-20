import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput
import Mathlib.Analysis.Complex.ExponentialBounds

/-! A uniform scalar recurrence for actual soluble block compression.
The constant is deliberately coarse. Its logarithmic denominator is
retained through a block step instead of being replaced by a constant. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.LargeOrbitGeneratorNumerics

theorem sqrt_linear_le_binary_exp (a : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (1 + a) * (1 + a / 8) ≤ (2 : ℝ) ^ a := by
  have hs : Real.sqrt (1 + a) ≤ Real.exp (a / 2) := by
    rw [Real.exp_half]
    exact Real.sqrt_le_sqrt (by linarith [Real.add_one_le_exp a])
  calc
    Real.sqrt (1 + a) * (1 + a / 8) ≤
        Real.exp (a / 2) * Real.exp (a / 8) :=
      mul_le_mul hs (by linarith [Real.add_one_le_exp (a / 8)])
        (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (5 * a / 8) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (Real.log 2 * a) := by
      apply Real.exp_le_exp.mpr
      have hlog : (5 : ℝ) / 8 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      nlinarith
    _ = (2 : ℝ) ^ a := (Real.rpow_def_of_pos (by norm_num) _).symm

theorem normalized_block_recurrence (a b : ℝ) (ha : 0 ≤ a) (hb : 1 ≤ b) :
    ((40 : ℝ) / 3 * a + 128) * Real.sqrt (a + b) ≤
      128 * (2 : ℝ) ^ a * Real.sqrt b := by
  have hb0 : 0 ≤ b := by linarith
  have hs : Real.sqrt (a + b) ≤ Real.sqrt b * Real.sqrt (1 + a) := by
    rw [← Real.sqrt_mul hb0]
    apply Real.sqrt_le_sqrt
    nlinarith
  calc
    ((40 : ℝ) / 3 * a + 128) * Real.sqrt (a + b) ≤
        (128 * (1 + a / 8)) * (Real.sqrt b * Real.sqrt (1 + a)) := by
      apply mul_le_mul _ hs (Real.sqrt_nonneg _) (by positivity)
      nlinarith
    _ = (128 * Real.sqrt b) * (Real.sqrt (1 + a) * (1 + a / 8)) := by ring
    _ ≤ (128 * Real.sqrt b) * (2 : ℝ) ^ a :=
      mul_le_mul_of_nonneg_left (sqrt_linear_le_binary_exp a ha) (by positivity)
    _ = _ := by ring

theorem logb_le_square {s : ℝ} (hs : 2 ≤ s) : Real.logb 2 s ≤ s ^ 2 := by
  have hlog : (5 : ℝ) / 8 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have h := Real.log_le_sub_one_of_pos (by linarith : 0 < s)
  nlinarith [sq_nonneg (s - 1), mul_nonneg (sq_nonneg s)
    (show 0 ≤ Real.log 2 - 5 / 8 by linarith)]

theorem induced_ceiling_le_five (s : ℕ) (hs : 2 ≤ s) :
    (traceyInducedGeneratorCeiling 1 s : ℝ) ≤
      5 * s / Real.sqrt (Real.logb 2 s) := by
  have hsreal : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hslog : 0 < Real.logb 2 s :=
    Real.logb_pos (by norm_num) (by linarith)
  have hsqrt : 0 < Real.sqrt (Real.logb 2 s) := Real.sqrt_pos.mpr hslog
  have hsqrtle : Real.sqrt (Real.logb 2 s) ≤ s := by
    exact (Real.sqrt_le_iff).mpr ⟨by positivity, logb_le_square hsreal⟩
  have hunit : (1 : ℝ) ≤ s / Real.sqrt (Real.logb 2 s) :=
    (le_div_iff₀ hsqrt).mpr (by simpa using hsqrtle)
  have hceil := (Nat.ceil_lt_add_one
    (show 0 ≤ 4 * (1 : ℝ) * s / Real.sqrt (Real.logb 2 s) by positivity)).le
  unfold traceyInducedGeneratorCeiling
  norm_num only [Nat.cast_one, mul_one] at hceil ⊢
  calc
    _ ≤ 4 * (s : ℝ) / Real.sqrt (Real.logb 2 s) + 1 := hceil
    _ = (4 * s + Real.sqrt (Real.logb 2 s)) / Real.sqrt (Real.logb 2 s) := by
      field_simp
    _ ≤ _ := (div_le_div_iff_of_pos_right hsqrt).mpr (by linarith)


/-- The same scalar potential also pays a primitive head directly. -/
theorem primitive_log_recurrence (r : ℕ) (hr : 2 ≤ r) :
    Real.logb 2 r + 2 ≤ 128 * r / Real.sqrt (Real.logb 2 r) := by
  let a := Real.logb 2 r
  have hrreal : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have ha : 1 ≤ a := by
    dsimp [a]
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact (Real.logb_le_logb (by norm_num) (by norm_num) (by linarith)).mpr hrreal
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr (by linarith)
  apply (le_div_iff₀ hs).mpr
  have hnum := normalized_block_recurrence a 1 (by linarith) le_rfl
  simp only [Real.sqrt_one, mul_one] at hnum
  have hpow : (2 : ℝ) ^ a = r :=
    Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  rw [hpow] at hnum
  calc
    (a + 2) * Real.sqrt a ≤
        ((40 : ℝ) / 3 * a + 128) * Real.sqrt (a + 1) :=
      mul_le_mul (by linarith) (Real.sqrt_le_sqrt (by linarith))
        (Real.sqrt_nonneg _) (by positivity)
    _ ≤ _ := hnum

theorem primitive_natLog_recurrence (r : ℕ) (hr : 2 ≤ r) :
    (Nat.log2 r : ℝ) + 2 ≤ 128 * r / Real.sqrt (Real.logb 2 r) :=
  by linarith [Real.log2_le_logb r, primitive_log_recurrence r hr]

/-- One scalar constant works for every nontrivial local block and top.
It pays the full primitive composition estimate and the retained top. -/
theorem block_recurrence (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) :
    (traceyInducedGeneratorCeiling 1 s : ℝ) *
        ((8 : ℝ) / 3 * Real.logb 2 r - 4 / 3) +
      128 * s / Real.sqrt (Real.logb 2 s) ≤
        128 * (r * s : ℕ) / Real.sqrt (Real.logb 2 (r * s : ℕ)) := by
  let a := Real.logb 2 r
  let b := Real.logb 2 s
  have hrreal : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hsreal : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have ha : 1 ≤ a := by
    dsimp [a]
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact (Real.logb_le_logb (by norm_num) (by norm_num) (by linarith)).mpr hrreal
  have hb : 1 ≤ b := by
    dsimp [b]
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact (Real.logb_le_logb (by norm_num) (by norm_num) (by linarith)).mpr hsreal
  have hbpos : 0 < Real.sqrt b := Real.sqrt_pos.mpr (by linarith)
  have habpos : 0 < Real.sqrt (a + b) := Real.sqrt_pos.mpr (by linarith)
  have hnum := normalized_block_recurrence a b (by linarith) hb
  have hpow : (2 : ℝ) ^ a = r :=
    Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  have hscaled :
      ((40 : ℝ) / 3 * a + 128) * (s : ℝ) / Real.sqrt b ≤
        128 * r * s / Real.sqrt (a + b) := by
    rw [div_le_div_iff₀ hbpos habpos]
    rw [hpow] at hnum
    nlinarith [mul_le_mul_of_nonneg_right hnum (show (0 : ℝ) ≤ s by positivity)]
  have hB : (traceyInducedGeneratorCeiling 1 s : ℝ) ≤ 5 * s / Real.sqrt b :=
    induced_ceiling_le_five s hs
  have hB0 : 0 ≤ (traceyInducedGeneratorCeiling 1 s : ℝ) := by positivity
  have hfirst :
      (traceyInducedGeneratorCeiling 1 s : ℝ) * ((8 : ℝ) / 3 * a - 4 / 3) +
        128 * s / Real.sqrt b ≤ ((40 : ℝ) / 3 * a + 128) * s / Real.sqrt b := by
    have hmul := mul_le_mul_of_nonneg_right hB (show 0 ≤ (8 : ℝ) / 3 * a by linarith)
    have heq : (5 * (s : ℝ) / Real.sqrt b) * ((8 : ℝ) / 3 * a) +
        128 * s / Real.sqrt b = ((40 : ℝ) / 3 * a + 128) * s / Real.sqrt b := by ring
    rw [← heq]
    nlinarith
  have hlog : Real.logb 2 (r * s : ℕ) = a + b := by
    rw [Nat.cast_mul, Real.logb_mul (by linarith : (r : ℝ) ≠ 0)
      (by linarith : (s : ℝ) ≠ 0)]
  rw [hlog, Nat.cast_mul]
  simpa only [mul_assoc] using hfirst.trans hscaled

end SymmetricSubgroupAsymptotics.LargeOrbitGeneratorNumerics

end
