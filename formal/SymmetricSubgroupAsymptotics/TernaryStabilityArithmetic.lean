import SymmetricSubgroupAsymptotics.TernaryIndexWidthValues
import Mathlib.Tactic.Linarith

/-! Concrete degree envelopes for ternary relative stability. The degree
eighteen value is the sharper retained finite input; its total degree is
therefore bypassed by the scalar induction. No group/classification input
is used in this arithmetic module. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics

def ternaryStabilityBound (w : ℕ) : ℕ :=
  if w = 3 ∨ w = 4 then 1 else if w = 9 ∨ w = 18 then 2 else 5 * w / 27

@[simp] theorem ternaryStabilityBound_two : ternaryStabilityBound 2 = 0 := by
  norm_num [ternaryStabilityBound]

@[simp] theorem ternaryStabilityBound_three : ternaryStabilityBound 3 = 1 := by
  norm_num [ternaryStabilityBound]

@[simp] theorem ternaryStabilityBound_four : ternaryStabilityBound 4 = 1 := by
  norm_num [ternaryStabilityBound]

@[simp] theorem ternaryStabilityBound_nine : ternaryStabilityBound 9 = 2 := by
  norm_num [ternaryStabilityBound]

@[simp] theorem ternaryStabilityBound_eighteen : ternaryStabilityBound 18 = 2 := by
  norm_num [ternaryStabilityBound]

theorem ternaryStability_base_le (w : ℕ) (h18 : w ≠ 18) :
    5 * w / 27 ≤ ternaryStabilityBound w := by
  by_cases h3 : w = 3
  · subst w; norm_num [ternaryStabilityBound]
  by_cases h4 : w = 4
  · subst w; norm_num [ternaryStabilityBound]
  by_cases h9 : w = 9
  · subst w; norm_num [ternaryStabilityBound]
  simp [ternaryStabilityBound, h3, h4, h9, h18]

theorem ternaryStability_le_base (w : ℕ) (h3 : w ≠ 3) (h4 : w ≠ 4) (h9 : w ≠ 9) :
    ternaryStabilityBound w ≤ 5 * w / 27 := by
  by_cases h18 : w = 18
  · subst w; norm_num [ternaryStabilityBound]
  simp [ternaryStabilityBound, h3, h4, h9, h18]

theorem ternaryStrictHead_le_stability_base (d w : ℕ) (h : 20 * d < 3 * w) :
    d ≤ 5 * w / 27 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 27)).mpr
  omega

private theorem stability_div_three (r : ℕ) : (r / 3) * 3 ≤ r :=
  Nat.div_mul_le_self r 3

private theorem stability_width_three (s : ℕ) (hs : 3 ≤ s) :
    ternaryIndexWidth s * 3 ≤ s :=
  (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mp (ternaryIndexWidth_le_third s hs)

/-- The concrete stability recurrence. The sole bypass is the actual
total degree eighteen, whose sharper value two is a finite group input. -/
theorem ternaryStability_scalar (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s)
    (h18 : r * s ≠ 18) :
    (r / 3) * ternaryIndexWidth s + ternaryStabilityBound s ≤
      ternaryStabilityBound (r * s) := by
  have hv := stability_div_three r
  by_cases hs2 : s = 2
  · subst s
    rw [ternaryIndexWidth_two, ternaryStabilityBound_two, mul_one, add_zero]
    apply le_trans ?_ (ternaryStability_base_le _ h18)
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 27)).mpr
    nlinarith
  by_cases hs3 : s = 3
  · subst s
    rw [ternaryIndexWidth_three, ternaryStabilityBound_three, mul_one]
    by_cases hr2 : r = 2
    · subst r; norm_num [ternaryStabilityBound]
    by_cases hr3 : r = 3
    · subst r; norm_num [ternaryStabilityBound]
    by_cases hr4 : r = 4
    · subst r; norm_num [ternaryStabilityBound]
    have hr5 : 5 ≤ r := by omega
    apply le_trans ?_ (ternaryStability_base_le _ h18)
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 27)).mpr
    nlinarith
  by_cases hs4 : s = 4
  · subst s
    rw [ternaryIndexWidth_four, ternaryStabilityBound_four, mul_one]
    by_cases hr2 : r = 2
    · subst r; norm_num [ternaryStabilityBound]
    have hr3 : 3 ≤ r := by omega
    apply le_trans ?_ (ternaryStability_base_le _ h18)
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 27)).mpr
    nlinarith
  by_cases hs9 : s = 9
  · subst s
    rw [ternaryIndexWidth_nine, ternaryStabilityBound_nine]
    have hr3 : 3 ≤ r := by omega
    apply le_trans ?_ (ternaryStability_base_le _ h18)
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 27)).mpr
    nlinarith
  have hf := ternaryStability_le_base s hs3 hs4 hs9
  by_cases hr2 : r = 2
  · subst r
    simp only [show (2 : ℕ) / 3 = 0 by decide, zero_mul, zero_add]
    exact hf.trans ((Nat.div_le_div_right (by omega : 5 * s ≤ 5 * (2 * s))).trans
      (ternaryStability_base_le _ h18))
  have hr3 : 3 ≤ r := by omega
  have he := stability_width_three s (by omega)
  have hm := Nat.mul_le_mul hv he
  have ht := (Nat.le_div_iff_mul_le (by decide : 0 < 27)).mp hf
  have hsr := Nat.mul_le_mul_right s hr3
  apply le_trans ?_ (ternaryStability_base_le _ h18)
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 27)).mpr
  nlinarith

/-- For ordinary top degrees, every primitive block size at least four
is already strictly below the three-twentieths high-action threshold. -/
theorem ternaryStability_ordinary_high_exclusion (r s d : ℕ)
    (hr : 4 ≤ r) (hs : 3 ≤ s) (h3 : s ≠ 3) (h4 : s ≠ 4) (h9 : s ≠ 9)
    (hd : d ≤ (r / 3) * ternaryIndexWidth s + ternaryStabilityBound s) :
    20 * d < 3 * (r * s) := by
  have hv := stability_div_three r
  have he := stability_width_three s hs
  have ht := (Nat.le_div_iff_mul_le (by decide : 0 < 27)).mp
    (ternaryStability_le_base s h3 h4 h9)
  by_cases hr4 : r = 4
  · subst r
    norm_num at hd
    nlinarith
  have hr5 : 5 ≤ r := by omega
  have hm := Nat.mul_le_mul hv he
  have hsr := Nat.mul_le_mul_right s hr5
  nlinarith

/-- With ternary blocks, the sharp degree-eighteen top value removes
that scalar obstruction. Only child degrees 6,9,12,18,27 remain. -/
theorem ternaryStability_ternary_high_scalar (s : ℕ) (hs : 2 ≤ s)
    (h2 : s ≠ 2) (h3 : s ≠ 3) (h4 : s ≠ 4) (h6 : s ≠ 6) (h9 : s ≠ 9) :
    ternaryIndexWidth s + ternaryStabilityBound s ≤ 9 * s / 20 := by
  by_cases h18 : s = 18
  · subst s
    rw [ternaryIndexWidth_eighteen, ternaryStabilityBound_eighteen]
  have hf := ternaryStability_le_base s h3 h4 h9
  have hb : ternaryIndexWidth s + 5 * s / 27 ≤ 9 * s / 20 := by
    apply Nat.le_of_not_gt
    intro h
    rcases (ternaryIndexWidth_scalar_failure_iff s hs).mp h with h | h | h
    · exact h2 h
    · exact h6 h
    · exact h18 h
  exact (Nat.add_le_add_left hf _).trans hb

/-- Binary blocks have no ternary layer. Only a degree-three top can
meet the strict high-action test in this degree-only envelope. -/
theorem ternaryStability_binary_high_exclusion (s : ℕ) (hs : 2 ≤ s) (h3 : s ≠ 3) :
    20 * ternaryStabilityBound s < 3 * (2 * s) := by
  by_cases h4 : s = 4
  · subst s; norm_num
  by_cases h9 : s = 9
  · subst s; norm_num
  have ht := (Nat.le_div_iff_mul_le (by decide : 0 < 27)).mp
    (ternaryStability_le_base s h3 h4 h9)
  nlinarith

end SymmetricSubgroupAsymptotics
