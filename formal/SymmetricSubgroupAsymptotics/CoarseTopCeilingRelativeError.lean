import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Relative rounding errors for the literal coarse top ceiling. The
bounds are uniform intervals, not a census of integer top degrees. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CoarseTopCeilingRelativeError

theorem logb_le_sub_one (x : ℝ) (hx : 2 ≤ x) : Real.logb 2 x ≤ x-1 := by
  have hxpos : 0 < x := by linarith only [hx]
  have hh := Real.log_le_sub_one_of_pos (div_pos hxpos (by norm_num : (0 : ℝ) < 2))
  rw [Real.log_div hxpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hh
  have hl : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ x-2 by linarith only [hx])
  rw [Real.logb,div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  nlinarith only [hh,hm]

theorem logb_le_quarter_of_ge_sixteen (x : ℝ) (hx : 16 ≤ x) :
    Real.logb 2 x ≤ x/4 := by
  have hxpos : 0 < x := by linarith only [hx]
  have hh := Real.log_le_sub_one_of_pos (div_pos hxpos (by norm_num : (0 : ℝ) < 16))
  rw [Real.log_div hxpos.ne' (by norm_num : (16 : ℝ) ≠ 0),
    show Real.log (16 : ℝ) = 4*Real.log 2 by
      rw [show (16 : ℝ) = 2^4 by norm_num,Real.log_pow]; norm_num] at hh
  have hl : (1/4 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ x-16 by linarith only [hx])
  rw [Real.logb,div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  nlinarith only [hh,hm]

private theorem ceil_le_of_sqrt_le (t : ℕ) (k : ℝ) (ht : 2 ≤ t) (hk : 0 < k)
    (hs : Real.sqrt (Real.logb 2 (t : ℝ)) ≤ (t : ℝ)/k) :
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) ≤
      (1+1/k)*((t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))) := by
  have hL : 0 < Real.logb 2 (t : ℝ) := Real.logb_pos (by norm_num)
    (by exact_mod_cast (show 1 < t by omega))
  have hroot := Real.sqrt_pos.mpr hL
  have hunit : k ≤ (t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ)) := by
    apply (le_div_iff₀ hroot).mpr
    have hh := (le_div_iff₀ hk).mp hs
    simpa only [mul_comm] using hh
  have hceil : (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) ≤
      (t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))+1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have herror : (1 : ℝ) ≤ ((t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ)))/k :=
    (le_div_iff₀ hk).mpr (by simpa only [one_mul] using hunit)
  calc
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) ≤
        (t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))+1 := hceil
    _ ≤ (t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))+
        ((t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ)))/k := add_le_add le_rfl herror
    _ = (1+1/k)*((t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))) := by ring

theorem ceil_le_three_halves (t : ℕ) (ht : 2 ≤ t) :
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) ≤
      (3/2)*((t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))) := by
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hlog := logb_le_sub_one (t : ℝ) htR
  have hroot : Real.sqrt (Real.logb 2 (t : ℝ)) ≤ (t : ℝ)/2 := by
    apply (Real.sqrt_le_iff).mpr ⟨by positivity,?_⟩
    nlinarith only [hlog,sq_nonneg ((t : ℝ)-2)]
  have he : (1+1/(2 : ℝ)) = 3/2 := by norm_num
  simpa only [he] using ceil_le_of_sqrt_le t 2 ht (by norm_num) hroot

theorem ceil_le_nine_eighths (t : ℕ) (ht : 16 ≤ t) :
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) ≤
      (9/8)*((t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))) := by
  have htR : (16 : ℝ) ≤ t := by exact_mod_cast ht
  have hlog := logb_le_quarter_of_ge_sixteen (t : ℝ) htR
  have hroot : Real.sqrt (Real.logb 2 (t : ℝ)) ≤ (t : ℝ)/8 := by
    apply (Real.sqrt_le_iff).mpr ⟨by positivity,?_⟩
    have hp : 0 ≤ (t : ℝ)*((t : ℝ)-16) := mul_nonneg (by positivity)
      (by linarith only [htR])
    nlinarith only [hlog,hp]
  have he : (1+1/(8 : ℝ)) = 9/8 := by norm_num
  simpa only [he] using ceil_le_of_sqrt_le t 8 (by omega) (by norm_num) hroot

end SymmetricSubgroupAsymptotics.CoarseTopCeilingRelativeError
