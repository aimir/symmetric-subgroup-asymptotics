import SymmetricSubgroupAsymptotics.BinaryChainCentralBinomialBudget

/-! A uniform scalar tail for a binary defining-primary affine fibre.
The coefficient is the genuine triangular defining-prime valuation,
not the coarser square-dimension order bound. The top term is displayed
explicitly: this file proves no top generator theorem and assumes no
Tracey or McIver--Neumann input. The finite window
`e < 20` or `e < 12*d` is deliberately left outside the conclusion. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineDefiningPrimaryTailNumerics

/-- The triangular leading coefficient has a uniform positive margin. -/
theorem triangular_margin (d : ℕ) (hd : 1 ≤ d) :
    5 * d * (d + 1) + 12 ≤ 11 * 2 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
      have hdd : d ≤ d*d := by nlinarith
      rw [pow_succ]
      nlinarith

/-- A polynomial absorption estimate, proved by induction rather than
a finite parameter table. -/
theorem cubic_absorption (e : ℕ) (he : 20 ≤ e) :
    24 * (e + 1) ^ 3 ≤ 2 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih =>
      have hsq : 400 ≤ e^2 := by nlinarith
      have hcube := Nat.mul_le_mul_left e hsq
      have hstep : (e + 2)^3 ≤ 2*(e + 1)^3 := by nlinarith
      calc
        24 * (e + 1 + 1)^3 ≤ 2*(24*(e + 1)^3) := by nlinarith
        _ ≤ 2 * 2^e := Nat.mul_le_mul_left 2 ih
        _ = 2^(e+1) := by rw [pow_succ]; omega

/-- For sufficiently large binary top exponent relative to the fibre
dimension, the actual primary coefficient, a coarse constant-one top
term, and a square-dimension lower-order allowance fit the constant-one
bound at the original product degree. This is a scalar implication only. -/
theorem binary_primary_tail (d e : ℕ) (hd : 1 ≤ d)
    (he : 20 ≤ e) (hde : 12*d ≤ e) :
    (((d : ℝ) * (d + 1) / 2) * (e.choose (e/2) : ℝ) +
        (2 : ℝ)^e / Real.sqrt e + (d : ℝ)^2 + 1) *
      Real.sqrt ((d+e : ℕ) : ℝ) ≤ (2 : ℝ)^(d+e) := by
  have heR : (20 : ℝ) ≤ e := by exact_mod_cast he
  have hdeR : 12*(d : ℝ) ≤ e := by exact_mod_cast hde
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hroot : 0 < Real.sqrt (e : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hs := Real.sq_sqrt (Nat.cast_nonneg e)
  have hds := Real.sq_sqrt (Nat.cast_nonneg (d+e))
  let a : ℝ := ((d : ℝ)*(d+1)/2)*(e.choose (e/2) : ℝ) +
    (2 : ℝ)^e / Real.sqrt e
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hmargin : ((d : ℝ)*(d+1)/2)*(5/6) + 1 ≤
      (11/12 : ℝ)*(2 : ℝ)^d := by
    have hh : 5*(d : ℝ)*(d+1)+12 ≤ 11*(2 : ℝ)^d := by
      exact_mod_cast triangular_margin d hd
    nlinarith
  have hb := BinaryChainCentralBinomialBudget.middle_mul_sqrt_le e
  change (e.choose (e/2) : ℝ)*Real.sqrt e ≤ (5/6 : ℝ)*(2 : ℝ)^e at hb
  have hb' := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (d : ℝ)*(d+1)/2 by positivity)
  have hm := mul_le_mul_of_nonneg_right hmargin
    (show 0 ≤ (2 : ℝ)^e by positivity)
  have hmain : a*Real.sqrt e ≤ (11/12 : ℝ)*(2 : ℝ)^(d+e) := by
    have ht : ((2 : ℝ)^e / Real.sqrt e)*Real.sqrt e = (2 : ℝ)^e :=
      div_mul_cancel₀ _ hroot.ne'
    dsimp [a]
    rw [add_mul, ht, pow_add]
    nlinarith
  have hscale : 22*Real.sqrt ((d+e : ℕ) : ℝ) ≤ 23*Real.sqrt (e : ℝ) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, hds, hs]
    push_cast
    nlinarith
  have hscale' := mul_le_mul_of_nonneg_left hscale ha
  have hmain' : a*Real.sqrt ((d+e : ℕ) : ℝ) ≤
      (23/24 : ℝ)*(2 : ℝ)^(d+e) := by nlinarith
  have hsle : Real.sqrt ((d+e : ℕ) : ℝ) ≤ (e : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · push_cast
      nlinarith
  have hexp : 24*((e : ℝ)+1)^3 ≤ (2 : ℝ)^e := by
    exact_mod_cast cubic_absorption e he
  have hpoly : ((d : ℝ)^2+1)*(e : ℝ) ≤ ((e : ℝ)+1)^3 := by
    have hsq : (d : ℝ)^2 ≤ (e : ℝ)^2 :=
      pow_le_pow_left₀ hd0 (by linarith) 2
    have hh := mul_le_mul_of_nonneg_right hsq (show (0 : ℝ) ≤ e by positivity)
    nlinarith
  have hp := mul_le_mul_of_nonneg_left hsle
    (show 0 ≤ (d : ℝ)^2+1 by positivity)
  have hpower : (2 : ℝ)^e ≤ (2 : ℝ)^(d+e) := by
    rw [pow_add]
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  have hsmall : ((d : ℝ)^2+1)*Real.sqrt ((d+e : ℕ) : ℝ) ≤
      (1/24 : ℝ)*(2 : ℝ)^(d+e) := by nlinarith
  change (a + (d : ℝ)^2 + 1)*Real.sqrt ((d+e : ℕ) : ℝ) ≤ _
  nlinarith

end SymmetricSubgroupAsymptotics.BinaryAffineDefiningPrimaryTailNumerics
