import SymmetricSubgroupAsymptotics.TinyComplementHigherPolynomialBudgets

/-! Uniform scalar envelopes for the binary tiny-complement family and
the two genuine dominant-ternary degree shapes. The binary rounding
term retains the actual top degree three times its binary primary;
the ternary estimates retain the literal three/six-point top ceilings. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TinyComplementHigherEnvelopes
open TinyComplementHigherPolynomialBudgets

theorem binary_envelope_le (d : ℕ) (hd : 4 ≤ d) (M m C u L : ℝ)
    (hM : 4 ≤ M) (hm0 : 0 ≤ m) (hmA : m ≤ (d : ℝ)*((d : ℝ)+1)/2)
    (hmC : m ≤ C) (hC : C ≤ (d : ℝ)^2-2) (hu : u ≤ 1/3)
    (hL : 7/2 ≤ L) (hLhi : L ≤ 33/5) :
    (m*u+(C-m)/M+1/(3*M))*Real.sqrt ((d : ℝ)+L)+
      Real.sqrt (1+(d : ℝ)/L) ≤ (2 : ℝ)^d := by
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hM0 : 0 < M := by linarith only [hM]
  have hfirst : m*u ≤ m/3 := by
    simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hu hm0
  have hrest0 : 0 ≤ C-m+1/3 := by linarith only [hmC]
  have hrest := div_le_div_of_nonneg_left hrest0 (by norm_num : (0 : ℝ) < 4) hM
  have hslope := mul_le_mul_of_nonneg_right hmA (by norm_num : (0 : ℝ) ≤ 1/12)
  have htotal := div_le_div_of_nonneg_right hC (by norm_num : (0 : ℝ) ≤ 4)
  have hrate : m*u+(C-m)/M+1/(3*M) ≤
      7*(d : ℝ)^2/24+(d : ℝ)/24-5/12 := by
    calc
      m*u+(C-m)/M+1/(3*M) = m*u+(C-m+1/3)/M := by ring
      _ ≤ m/3+(C-m+1/3)/4 := add_le_add hfirst hrest
      _ = m/12+C/4+1/12 := by ring
      _ ≤ ((d : ℝ)*((d : ℝ)+1)/2)/12+((d : ℝ)^2-2)/4+1/12 := by
        linarith only [hslope,htotal]
      _ = 7*(d : ℝ)^2/24+(d : ℝ)/24-5/12 := by ring
  have hcoef0 : 0 ≤ 7*(d : ℝ)^2/24+(d : ℝ)/24-5/12 := by
    nlinarith only [sq_nonneg (d : ℝ),hdR]
  have hroot : Real.sqrt ((d : ℝ)+L) ≤ (10*(d : ℝ)+91)/40 := by
    have hprod : 0 ≤ ((d : ℝ)-4)*(100*(d : ℝ)+620) :=
      mul_nonneg (by linarith only [hdR]) (by positivity)
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [hprod,hLhi]
  have hmain := mul_le_mul hrate hroot (Real.sqrt_nonneg _) hcoef0
  have htop : Real.sqrt (1+(d : ℝ)/L) ≤ ((d : ℝ)+11)/10 := by
    have hh := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ d by positivity)
      (by norm_num : (0 : ℝ) < 7/2) hL
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [hh,sq_nonneg (7*(d : ℝ)-23)]
  calc
    (m*u+(C-m)/M+1/(3*M))*Real.sqrt ((d : ℝ)+L)+
        Real.sqrt (1+(d : ℝ)/L) ≤ binary d := by
      dsimp only [binary]
      linarith only [hmain,htop]
    _ ≤ (2 : ℝ)^d := binary_le d hd

theorem ternary_three_scaled_le (d : ℕ) (hd : 4 ≤ d) (g L : ℝ)
    (hg : g ≤ (d : ℝ)^2+(d : ℝ)/2) (hL : L ≤ 2) :
    g*Real.sqrt ((d : ℝ)+L) ≤ 3*(2 : ℝ)^d := by
  have hroot : Real.sqrt ((d : ℝ)+L) ≤ ((d : ℝ)+6)/4 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [hL,sq_nonneg ((d : ℝ)-2)]
  have hh := mul_le_mul hg hroot (Real.sqrt_nonneg _)
    (show 0 ≤ (d : ℝ)^2+(d : ℝ)/2 by positivity)
  calc
    g*Real.sqrt ((d : ℝ)+L) ≤ ternaryThree d := by
      dsimp only [ternaryThree]
      convert hh using 1 <;> ring
    _ ≤ 3*(2 : ℝ)^d := ternaryThree_le d hd

theorem ternary_six_scaled_le (d : ℕ) (hd : 4 ≤ d) (g L : ℝ)
    (hg : g ≤ 2*(d : ℝ)^2+(d : ℝ)-2) (hL : L ≤ 3) :
    g*Real.sqrt ((d : ℝ)+L) ≤ 6*(2 : ℝ)^d := by
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hroot : Real.sqrt ((d : ℝ)+L) ≤ ((d : ℝ)+7)/4 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [hL,sq_nonneg ((d : ℝ)-1)]
  have hcoef0 : 0 ≤ 2*(d : ℝ)^2+(d : ℝ)-2 := by
    nlinarith only [sq_nonneg (d : ℝ),hdR]
  have hh := mul_le_mul hg hroot (Real.sqrt_nonneg _) hcoef0
  calc
    g*Real.sqrt ((d : ℝ)+L) ≤ ternarySix d := by
      dsimp only [ternarySix]
      convert hh using 1 <;> ring
    _ ≤ 6*(2 : ℝ)^d := ternarySix_le d hd

end SymmetricSubgroupAsymptotics.TinyComplementHigherEnvelopes
