import SymmetricSubgroupAsymptotics.TinyPrimeTopSharpFloorNumerics

/-! Rational logarithmic certificates for the published sharp floor.
The only numerical input is a real squared budget, so dyadic bounds
on powers of the original degree can be shared by small consumers. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.TraceySharpLogSquareNumerics
open TraceySharpHalfDegreeNumerics

theorem le_sharpFloor_of_log_square (n k : ℕ) (hn : 2 ≤ n)
    (hb : (4:ℝ)*k^2*Real.logb 2 n ≤ 3*(n:ℝ)^2) : k ≤ sharpFloor n := by
  have hL : 0 < Real.logb 2 (n:ℝ) := Real.logb_pos (by norm_num)
    (by exact_mod_cast (show 1 < n by omega))
  have hs := Real.sq_sqrt hL.le
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hsq : (2*(k:ℝ)*Real.sqrt (Real.logb 2 n))^2 ≤
      (Real.sqrt 3*(n:ℝ))^2 := by
    calc
      (2*(k:ℝ)*Real.sqrt (Real.logb 2 n))^2 =
          4*(k:ℝ)^2*(Real.sqrt (Real.logb 2 n))^2 := by ring
      _ = 4*(k:ℝ)^2*Real.logb 2 n := by rw [hs]
      _ ≤ 3*(n:ℝ)^2 := hb
      _ = (Real.sqrt 3*(n:ℝ))^2 := by rw [mul_pow,h3]
  have hnum : 2*(k:ℝ)*Real.sqrt (Real.logb 2 n) ≤ Real.sqrt 3*(n:ℝ) := by
    nlinarith only [hsq,show 0 ≤ 2*(k:ℝ)*Real.sqrt (Real.logb 2 n) by positivity,
      show 0 ≤ Real.sqrt 3*(n:ℝ) by positivity]
  apply Nat.le_floor
  apply (le_div_iff₀ (show 0 < 2*Real.sqrt (Real.logb 2 n) by positivity)).mpr
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hnum

theorem logb_le_half_of_square_le_pow (n b : ℕ) (hn : 0 < n) (hb : n^2 ≤ 2^b) :
    Real.logb 2 (n:ℝ) ≤ (b:ℝ)/2 := by
  have h := TinyPrimeTopSharpFloorNumerics.log_le_of_pow (n^2) b (by positivity) hb
  have he : Real.logb 2 ((n^2:ℕ):ℝ) = 2*Real.logb 2 (n:ℝ) := by
    rw [Nat.cast_pow,Real.logb_pow]
    norm_num
  rw [he] at h
  linarith

end SymmetricSubgroupAsymptotics.TraceySharpLogSquareNumerics
