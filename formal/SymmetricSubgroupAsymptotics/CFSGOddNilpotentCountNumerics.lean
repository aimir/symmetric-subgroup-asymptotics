import SymmetricSubgroupAsymptotics.CFSGNilpotentCountBudgets
import SymmetricSubgroupAsymptotics.CFSGOddNilpotentBoundedSkeletonCount

/-! Convert the proved native odd-nilpotent count to a fixed-cutoff
quadratic bound with an `O_C(b log b)` error. No unrestricted subgroup
estimate is used in this conversion. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGNilpotentCountBudgets
open MarkedC4

def oddMenuCoefficient (C : ℕ) : ℝ :=
  3 + (max C 1 : ℕ) + (ActualBinarySkeletonMenu.letterBound C : ℕ) + (2 ^ C.factorial : ℕ)

def oddCoefficient (C : ℕ) : ℝ := oddMenuCoefficient C + (C.factorial : ℝ) ^ 2

theorem oddCoefficient_nonneg (C : ℕ) : 0 ≤ oddCoefficient C := by
  unfold oddCoefficient oddMenuCoefficient
  positivity

theorem odd_native_prefactor_le (C b : ℕ) (hb : 1 ≤ b) :
    (b.factorial * ((b + 1) * (max C 1) ^ b *
      (ActualBinarySkeletonMenu.letterBound C) ^ b) *
      (b.factorial * (b + 1) ^ ((2 ^ C.factorial) * b)) : ℝ) ≤
        (2 : ℝ) ^ (oddMenuCoefficient C * b * degreeLog b) := by
  have hf := factorial_le_budget b
  have hg : (b + 1 : ℝ) ≤ (2 : ℝ) ^ ((b : ℝ) * degreeLog b) := by
    have h := power_le_budget (b + 1) 1 b (by omega)
    simp only [Nat.cast_add, Nat.cast_one, pow_one, one_mul] at h
    apply h.trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
    exact le_mul_of_one_le_left (le_trans (by norm_num) (one_le_degreeLog b)) hbR
  have hm := constant_power_le_budget (max C 1) b
  have hl := constant_power_le_budget (ActualBinarySkeletonMenu.letterBound C) b
  have hp := power_le_budget (b + 1) ((2 ^ C.factorial) * b) b (by omega)
  have h₁ := mul_pow2_bounds hf hg (by positivity)
  have h₂ := mul_pow2_bounds h₁ hm (by positivity)
  have h₃ := mul_pow2_bounds h₂ hl (by positivity)
  have h₄ := mul_pow2_bounds h₃ hf (by positivity)
  have h₅ := mul_pow2_bounds h₄ hp (by positivity)
  convert h₅ using 1
  · push_cast
    ring
  · congr 1
    unfold oddMenuCoefficient
    push_cast
    ring

theorem odd_nilpotent_card_le (C b : ℕ) :
    (Nat.card (CFSGNilpotentBinaryOddConvolution.OddFamily C b) : ℝ) ≤
      (2 : ℝ) ^ ((b : ℝ) ^ 2 / 16 + oddCoefficient C * b * degreeLog b) := by
  by_cases hb : b = 0
  · subst b
    simpa only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
      mul_zero, zero_mul, add_zero, Real.rpow_zero] using
      zero_family_card_le_one (fun O => Group.IsNilpotent O ∧
        ¬ 2 ∣ Nat.card O ∧ OrbitCutoffFamilies.OrbitCutoff C O)
  · have hp := odd_native_prefactor_le C b (by omega)
    have hn := CFSGOddNilpotentBoundedSkeletonCount.bounded_odd_nilpotent_card_le C b
    have hpow := mul_pow2_bounds hp
      (le_rfl : (2 : ℝ) ^ ((b : ℝ) ^ 2 / 16 + b * (C.factorial : ℝ) ^ 2) ≤ _)
      (by positivity)
    have hcost : oddMenuCoefficient C * b * degreeLog b +
        ((b : ℝ) ^ 2 / 16 + b * (C.factorial : ℝ) ^ 2) ≤
          (b : ℝ) ^ 2 / 16 + oddCoefficient C * b * degreeLog b := by
      have hm := mul_le_mul_of_nonneg_left (one_le_degreeLog b)
        (show 0 ≤ (b : ℝ) * (C.factorial : ℝ) ^ 2 by positivity)
      unfold oddCoefficient
      nlinarith
    have hnative :
        ((b.factorial * ((b + 1) * (max C 1) ^ b *
          (ActualBinarySkeletonMenu.letterBound C) ^ b) *
          (b.factorial * (b + 1) ^ ((2 ^ C.factorial) * b)) : ℕ) : ℝ) *
          (2 : ℝ) ^ ((b : ℝ) ^ 2 / 16 + b * (C.factorial : ℝ) ^ 2) ≤
        (2 : ℝ) ^ (oddMenuCoefficient C * b * degreeLog b +
          ((b : ℝ) ^ 2 / 16 + b * (C.factorial : ℝ) ^ 2)) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one] using hpow
    exact hn.trans (hnative.trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hcost))

end SymmetricSubgroupAsymptotics.CFSGNilpotentCountBudgets
