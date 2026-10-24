import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-! The complementary large-fibre scalar wedge for binary affine
ordinary costs. This estimate pays the genuine half-order coefficient
and a displayed allowance of two top-sized terms. No permutation group
bound, characteristic profile, or induction hypothesis is assumed here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineLargeDimensionWedgeNumerics

theorem cube_le_two_pow (d : ℕ) (hd : 10 ≤ d) : d^3 ≤ 2^d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
      have hs := Nat.mul_le_mul_left d hd
      have hc := Nat.mul_le_mul_left (d*d) hd
      have hstep : (d+1)^3 ≤ 2*d^3 := by nlinarith
      calc
        (d+1)^3 ≤ 2*d^3 := hstep
        _ ≤ 2*2^d := Nat.mul_le_mul_left 2 ih
        _ = 2^(d+1) := by rw [pow_succ]; omega

/-- A uniform estimate for every exponent in the small-relative-top
wedge. The proof uses induction only through `cube_le_two_pow`. -/
theorem coefficient_mul_sqrt_le (d e : ℕ) (hd : 10 ≤ d) (he : e ≤ 12*d) :
    (((d : ℝ)^2+d)/2+2)*Real.sqrt ((d+e : ℕ) : ℝ) ≤ (2 : ℝ)^d := by
  have hdR : (10 : ℝ) ≤ d := by exact_mod_cast hd
  have heR : (e : ℝ) ≤ 12*d := by exact_mod_cast he
  have hds : (10 : ℝ)*(d : ℝ) ≤ (d : ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_right hdR (Nat.cast_nonneg d)
    nlinarith
  have hcoeff : ((d : ℝ)^2+d)/2+2 ≤ (2/3 : ℝ)*(d : ℝ)^2 := by nlinarith
  have hroot : Real.sqrt ((d+e : ℕ) : ℝ) ≤ (3/2 : ℝ)*(d : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · push_cast
      nlinarith
  have hcube : (d : ℝ)^3 ≤ (2 : ℝ)^d := by exact_mod_cast cube_le_two_pow d hd
  calc
    _ ≤ ((2/3 : ℝ)*(d : ℝ)^2)*((3/2 : ℝ)*(d : ℝ)) :=
      mul_le_mul hcoeff hroot (Real.sqrt_nonneg _) (by positivity)
    _ = (d : ℝ)^3 := by ring
    _ ≤ (2 : ℝ)^d := hcube

/-- Multiplication by the literal top degree preserves the original
product-degree budget. This remains a scalar theorem only. -/
theorem half_order_wedge (d e : ℕ) (hd : 10 ≤ d) (he : e ≤ 12*d) :
    ((((d : ℝ)^2+d)/2+2)*(2 : ℝ)^e)*Real.sqrt ((d+e : ℕ) : ℝ) ≤
      (2 : ℝ)^(d+e) := by
  have hh := mul_le_mul_of_nonneg_right (coefficient_mul_sqrt_le d e hd he)
    (show 0 ≤ (2 : ℝ)^e by positivity)
  simpa only [pow_add, mul_right_comm] using hh

end SymmetricSubgroupAsymptotics.BinaryAffineLargeDimensionWedgeNumerics
