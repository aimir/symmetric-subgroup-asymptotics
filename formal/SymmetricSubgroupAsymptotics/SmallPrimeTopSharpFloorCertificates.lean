import SymmetricSubgroupAsymptotics.TinyPrimeTopSharpFloorNumerics

/-! Two exact integer/rational certificates for literal sharp floors.
At20 the integer logarithm ceiling5 is too coarse; the actual inequality
20^2<=2^9 gives log_2(20)<=9/2 before taking square roots. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallPrimeTopSharpFloorCertificates
open TraceySharpHalfDegreeNumerics

theorem four_le_sharpFloor_ten : 4 ≤ sharpFloor 10 :=
  TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square 10 4 4 (by decide)
    (TinyPrimeTopSharpFloorNumerics.log_le_of_pow 10 4 (by decide) (by decide)) (by decide)

theorem eight_le_sharpFloor_twenty : 8 ≤ sharpFloor 20 := by
  have hp : (20 : ℝ)^2 ≤ (2 : ℝ)^9 := by norm_num
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < (20 : ℝ)^2) hp
  simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hlog : Real.logb 2 (20 : ℝ) ≤ 9/2 := by linarith only [hl]
  have hroot : Real.sqrt (Real.logb 2 (20 : ℝ)) ≤ 15/7 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num,by linarith only [hlog]⟩
  have hthree : (12/7 : ℝ) ≤ Real.sqrt 3 := Real.le_sqrt_of_sq_le (by norm_num)
  have hpos : 0 < Real.logb 2 (20 : ℝ) := Real.logb_pos (by norm_num) (by norm_num)
  apply Nat.le_floor
  apply (le_div_iff₀ (show 0 < 2*Real.sqrt (Real.logb 2 (20 : ℝ)) by positivity)).mpr
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hroot,hthree]

end SymmetricSubgroupAsymptotics.SmallPrimeTopSharpFloorCertificates
