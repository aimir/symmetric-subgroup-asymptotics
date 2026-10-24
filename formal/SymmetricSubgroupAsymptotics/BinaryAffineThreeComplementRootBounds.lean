import SymmetricSubgroupAsymptotics.BinaryAffineThreeComplementMargins

/-! Root comparisons for complementary power three. The Wallis square
and the exact choose value at a single starting exponent are used
together. All later exponents use monotonicity, not a finite grid. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineThreeComplementRootBounds
open BinaryAffineThreeComplementMargins

private theorem scaled_square (a d : ℕ) (hd : 1 ≤ d) (B u K : ℝ)
    (hB : B ≤ 8/5) (hwall : u^2*(3*(a : ℝ)+2) ≤ 2) (hu : u^2 ≤ K) :
    u^2*((d : ℝ)+(a : ℝ)+B) ≤ 2/3+K*((d : ℝ)+14/15) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hh := mul_le_mul_of_nonneg_left hB (sq_nonneg u)
  have hrest := mul_le_mul_of_nonneg_right hu
    (show 0 ≤ (d : ℝ)+14/15 by linarith)
  nlinarith only [hh,hrest,hwall]

theorem matching_large (a d : ℕ) (hd : 3 ≤ d) (B u : ℝ)
    (hB0 : 0 ≤ B) (hB : B ≤ 8/5) (hu0 : 0 ≤ u) (hu : u ≤ 5/16)
    (hwall : u^2*(3*(a : ℝ)+2) ≤ 2) :
    u*Real.sqrt ((d : ℝ)+(a : ℝ)+B) ≤ ((d : ℝ)+18)/20 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hu2 : u^2 ≤ 25/256 := by
    have hh := (sq_le_sq₀ hu0 (by norm_num : (0 : ℝ) ≤ 5/16)).mpr hu
    norm_num only [div_pow] at hh
    exact hh
  have hh := scaled_square a d (by omega) B u (25/256) hB hwall hu2
  apply (sq_le_sq₀ (mul_nonneg hu0 (Real.sqrt_nonneg _)) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ)+(a : ℝ)+B)]
  nlinarith only [hh,sq_nonneg ((d : ℝ)-3),hdR]

theorem matching_short (a d : ℕ) (hd : 2 ≤ d) (B u : ℝ)
    (hB0 : 0 ≤ B) (hB : B ≤ 8/5) (hu0 : 0 ≤ u) (hu : u ≤ 35/128)
    (hwall : u^2*(3*(a : ℝ)+2) ≤ 2) :
    u*Real.sqrt ((d : ℝ)+(a : ℝ)+B) ≤ ((d : ℝ)+22)/25 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hu2 : u^2 ≤ 1225/16384 := by
    have hh := (sq_le_sq₀ hu0 (by norm_num : (0 : ℝ) ≤ 35/128)).mpr hu
    norm_num only [div_pow] at hh
    exact hh
  have hh := scaled_square a d (by omega) B u (1225/16384) hB hwall hu2
  apply (sq_le_sq₀ (mul_nonneg hu0 (Real.sqrt_nonneg _)) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ)+(a : ℝ)+B)]
  nlinarith only [hh,sq_nonneg ((d : ℝ)-2),hdR]

theorem matching_one (a : ℕ) (B u : ℝ) (hB0 : 0 ≤ B) (hB : B ≤ 8/5)
    (hu0 : 0 ≤ u) (hu : u ≤ 35/128) (hwall : u^2*(3*(a : ℝ)+2) ≤ 2) :
    u*Real.sqrt (1+(a : ℝ)+B) ≤ 91/100 := by
  have hu2 : u^2 ≤ 1225/16384 := by
    have hh := (sq_le_sq₀ hu0 (by norm_num : (0 : ℝ) ≤ 35/128)).mpr hu
    norm_num only [div_pow] at hh
    exact hh
  have hh := scaled_square a 1 (by decide) B u (1225/16384) hB hwall hu2
  apply (sq_le_sq₀ (mul_nonneg hu0 (Real.sqrt_nonneg _)) (by norm_num)).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1+(a : ℝ)+B)]
  norm_num only [Nat.cast_one] at hh
  nlinarith only [hh]

theorem error_large (a d : ℕ) (ha : 6 ≤ a) (hd : 1 ≤ d) :
    Real.sqrt ((a : ℝ)+(d : ℝ)+8/5)/(2 : ℝ)^a ≤ ((d : ℝ)+11)/256 := by
  have hh := shifted_error_antitone 6 a d (by decide) ha hd
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hbase : Real.sqrt ((6 : ℝ)+(d : ℝ)+8/5)/(2 : ℝ)^6 ≤ ((d : ℝ)+11)/256 := by
    norm_num only [show (2 : ℝ)^6 = 64 by norm_num]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 64)).mpr
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 6+(d : ℝ)+8/5)]
    nlinarith only [sq_nonneg (d : ℝ),hdR]
  exact hh.trans hbase

theorem error_short (a d : ℕ) (ha : 8 ≤ a) (hd : 2 ≤ d) :
    Real.sqrt ((a : ℝ)+(d : ℝ)+8/5)/(2 : ℝ)^a ≤ ((d : ℝ)+12)/1024 := by
  have hh := shifted_error_antitone 8 a d (by decide) ha (by omega)
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hbase : Real.sqrt ((8 : ℝ)+(d : ℝ)+8/5)/(2 : ℝ)^8 ≤ ((d : ℝ)+12)/1024 := by
    norm_num only [show (2 : ℝ)^8 = 256 by norm_num]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 256)).mpr
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 8+(d : ℝ)+8/5)]
    nlinarith only [sq_nonneg (d : ℝ),hdR]
  exact hh.trans hbase

theorem error_one (a : ℕ) (ha : 7 ≤ a) :
    Real.sqrt ((a : ℝ)+1+8/5)/(2 : ℝ)^a ≤ 1/40 := by
  have hh := shifted_error_antitone 7 a 1 (by decide) ha (by decide)
  have hbase : Real.sqrt (48/5 : ℝ)/128 ≤ 1/40 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 128)).mpr
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 48/5)]
    norm_num
  simp only [Nat.cast_one,Nat.cast_ofNat,show (7 : ℝ)+1+8/5 = 48/5 by norm_num,
    show (2 : ℝ)^7 = 128 by norm_num] at hh
  exact hh.trans hbase

end SymmetricSubgroupAsymptotics.BinaryAffineThreeComplementRootBounds
