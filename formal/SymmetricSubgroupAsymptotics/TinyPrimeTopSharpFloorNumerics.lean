import SymmetricSubgroupAsymptotics.TraceySharpHalfDegreeNumerics

/-! Integer square certificates for the literal published sharp floor.
These are lower bounds on that floor, not replacements by the weaker
ordinary half-degree target. No permutation-group theorem is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TinyPrimeTopSharpFloorNumerics
open TraceySharpHalfDegreeNumerics

theorem le_sharpFloor_of_square (n k b : ℕ) (hn : 2 ≤ n)
    (hlog : Real.logb 2 (n : ℝ) ≤ b)
    (hbudget : 4 * k^2 * b ≤ 3 * n^2) : k ≤ sharpFloor n := by
  let L := Real.logb 2 (n : ℝ)
  have hL : 0 < L := Real.logb_pos (by norm_num)
    (by exact_mod_cast (show 1 < n by omega))
  have hs : (Real.sqrt L)^2 = L := Real.sq_sqrt hL.le
  have h3 : (Real.sqrt (3 : ℝ))^2 = 3 := Real.sq_sqrt (by norm_num)
  have hb : (4 : ℝ) * (k : ℝ)^2 * b ≤ 3 * (n : ℝ)^2 := by exact_mod_cast hbudget
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (4 : ℝ)*(k : ℝ)^2 by positivity)
  have hleft : (2*(k : ℝ)*Real.sqrt L)^2 = 4*(k : ℝ)^2*L := by
    calc
      (2*(k : ℝ)*Real.sqrt L)^2 = 4*(k : ℝ)^2*(Real.sqrt L)^2 := by ring
      _ = 4*(k : ℝ)^2*L := by rw [hs]
  have hright : (Real.sqrt 3*(n : ℝ))^2 = 3*(n : ℝ)^2 := by
    rw [mul_pow,h3]
  have hsq : (2*(k : ℝ)*Real.sqrt L)^2 ≤ (Real.sqrt 3*(n : ℝ))^2 := by
    rw [hleft,hright]
    exact hm.trans hb
  have hnum : 2*(k : ℝ)*Real.sqrt L ≤ Real.sqrt 3*(n : ℝ) := by
    nlinarith only [hsq,show 0 ≤ 2*(k : ℝ)*Real.sqrt L by positivity,
      show 0 ≤ Real.sqrt 3*(n : ℝ) by positivity]
  apply Nat.le_floor
  apply (le_div_iff₀ (show 0 < 2*Real.sqrt L by positivity)).mpr
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hnum

theorem log_le_of_pow (n b : ℕ) (hn : 0 < n) (hpow : n ≤ 2^b) :
    Real.logb 2 (n : ℝ) ≤ b := by
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hn : (0 : ℝ) < n)
    (show (n : ℝ) ≤ (2 : ℝ)^b by exact_mod_cast hpow)
  simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
    using hh

theorem five_le_sharpFloor_twelve : 5 ≤ sharpFloor 12 :=
  le_sharpFloor_of_square 12 5 4 (by decide)
    (log_le_of_pow 12 4 (by decide) (by decide)) (by decide)

theorem six_le_sharpFloor_fifteen : 6 ≤ sharpFloor 15 :=
  le_sharpFloor_of_square 15 6 4 (by decide)
    (log_le_of_pow 15 4 (by decide) (by decide)) (by decide)

theorem eight_le_sharpFloor_twenty_one : 8 ≤ sharpFloor 21 :=
  le_sharpFloor_of_square 21 8 5 (by decide)
    (log_le_of_pow 21 5 (by decide) (by decide)) (by decide)

end SymmetricSubgroupAsymptotics.TinyPrimeTopSharpFloorNumerics
