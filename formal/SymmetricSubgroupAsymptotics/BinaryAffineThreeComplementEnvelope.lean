import SymmetricSubgroupAsymptotics.BinaryAffineThreeComplementRootBounds

/-! Two whole dimension/exponent ranges for complementary power three.
The joint total/matching coefficient is preserved throughout. The
uncovered small dimension-two exponents use actual shared-head bounds,
not an assumed improvement to these scalar coefficients. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineThreeComplementEnvelope
open BinaryAffineThreeComplementMargins BinaryAffineThreeComplementRootBounds

theorem joint_scaled_le (d : ℕ) (C m u L M k y : ℝ)
    (hm0 : 0 ≤ m) (hmC : m ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hmA : m ≤ (d : ℝ)*((d : ℝ)+1)/2) (hy : 0 ≤ y) (hky : y ≤ k)
    (hfirst : u*Real.sqrt ((d : ℝ)+L) ≤ k)
    (herror : Real.sqrt ((d : ℝ)+L)/M ≤ y) :
    (m*u+(C-m+1/3)/M)*Real.sqrt ((d : ℝ)+L) ≤
      ((d : ℝ)*((d : ℝ)+1)/2)*k+
        ((d : ℝ)^2-(d : ℝ)*((d : ℝ)+1)/2+1/3)*y := by
  have hother : 0 ≤ C-m+1/3 := by linarith only [hmC]
  have hprod := add_le_add (mul_le_mul_of_nonneg_left hfirst hm0)
    (mul_le_mul_of_nonneg_left herror hother)
  have hslope := mul_le_mul_of_nonneg_right hmA (sub_nonneg.mpr hky)
  have hh := mul_le_mul_of_nonneg_right hC hy
  calc
    (m*u+(C-m+1/3)/M)*Real.sqrt ((d : ℝ)+L) =
        m*(u*Real.sqrt ((d : ℝ)+L))+(C-m+1/3)*(Real.sqrt ((d : ℝ)+L)/M) := by ring
    _ ≤ m*k+(C-m+1/3)*y := hprod
    _ ≤ ((d : ℝ)*((d : ℝ)+1)/2)*k+
        ((d : ℝ)^2-(d : ℝ)*((d : ℝ)+1)/2+1/3)*y := by
      linarith only [hslope,hh]

theorem large_envelope_le (a d : ℕ) (ha : 6 ≤ a) (hd : 3 ≤ d)
    (C m B u L : ℝ) (hm0 : 0 ≤ m) (hmC : m ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hmA : m ≤ (d : ℝ)*((d : ℝ)+1)/2)
    (hB0 : 0 ≤ B) (hB : B ≤ 8/5) (hu0 : 0 ≤ u) (hu : u ≤ 5/16)
    (hwall : u^2*(3*(a : ℝ)+2) ≤ 2) (hL : 15/2 ≤ L) (hLupper : L ≤ (a : ℝ)+B) :
    (m*u+(C-m+1/3)/(2 : ℝ)^a)*Real.sqrt ((d : ℝ)+L)+
      Real.sqrt (1+(d : ℝ)/L) ≤ (2 : ℝ)^d := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hrad : (d : ℝ)+L ≤ (d : ℝ)+(a : ℝ)+B := by linarith only [hLupper]
  have hfirst : u*Real.sqrt ((d : ℝ)+L) ≤ ((d : ℝ)+18)/20 :=
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrad) hu0).trans
      (matching_large a d hd B u hB0 hB hu0 hu hwall)
  have hrad' : (d : ℝ)+L ≤ (a : ℝ)+(d : ℝ)+8/5 := by linarith only [hLupper,hB]
  have herror : Real.sqrt ((d : ℝ)+L)/(2 : ℝ)^a ≤ ((d : ℝ)+11)/256 :=
    (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hrad') (by positivity)).trans
      (error_large a d ha (by omega))
  have hmain := joint_scaled_le d C m u L ((2 : ℝ)^a)
    (((d : ℝ)+18)/20) (((d : ℝ)+11)/256) hm0 hmC hC hmA (by positivity)
    (by linarith only [hdR]) hfirst herror
  have htop : Real.sqrt (1+(d : ℝ)/L) ≤ 1+(d : ℝ)/15 := by
    have hh := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ d by positivity)
      (by norm_num : (0 : ℝ) < 15/2) hL
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith [sq_nonneg (d : ℝ)]
  calc
    (m*u+(C-m+1/3)/(2 : ℝ)^a)*Real.sqrt ((d : ℝ)+L)+
        Real.sqrt (1+(d : ℝ)/L) ≤ largeBudget d := by
      dsimp only [largeBudget]
      linarith only [hmain,htop]
    _ ≤ (2 : ℝ)^d := largeBudget_le d hd

theorem short_envelope_le (a d : ℕ) (ha : 8 ≤ a) (hd : 2 ≤ d)
    (C m B u L : ℝ) (hm0 : 0 ≤ m) (hmC : m ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hmA : m ≤ (d : ℝ)*((d : ℝ)+1)/2)
    (hB0 : 0 ≤ B) (hB : B ≤ 8/5) (hu0 : 0 ≤ u) (hu : u ≤ 35/128)
    (hwall : u^2*(3*(a : ℝ)+2) ≤ 2) (hL : 19/2 ≤ L) (hLupper : L ≤ (a : ℝ)+B) :
    (m*u+(C-m+1/3)/(2 : ℝ)^a)*Real.sqrt ((d : ℝ)+L)+
      Real.sqrt (1+(d : ℝ)/L) ≤ (2 : ℝ)^d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hrad : (d : ℝ)+L ≤ (d : ℝ)+(a : ℝ)+B := by linarith only [hLupper]
  have hfirst : u*Real.sqrt ((d : ℝ)+L) ≤ ((d : ℝ)+22)/25 :=
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrad) hu0).trans
      (matching_short a d hd B u hB0 hB hu0 hu hwall)
  have hrad' : (d : ℝ)+L ≤ (a : ℝ)+(d : ℝ)+8/5 := by linarith only [hLupper,hB]
  have herror : Real.sqrt ((d : ℝ)+L)/(2 : ℝ)^a ≤ ((d : ℝ)+12)/1024 :=
    (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hrad') (by positivity)).trans
      (error_short a d ha hd)
  have hmain := joint_scaled_le d C m u L ((2 : ℝ)^a)
    (((d : ℝ)+22)/25) (((d : ℝ)+12)/1024) hm0 hmC hC hmA (by positivity)
    (by linarith only [hdR]) hfirst herror
  have htop : Real.sqrt (1+(d : ℝ)/L) ≤ 1+251*(d : ℝ)/5000 := by
    have hh := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ d by positivity)
      (by norm_num : (0 : ℝ) < 19/2) hL
    have hprod : 0 ≤ (d : ℝ)*((d : ℝ)-2) := mul_nonneg (by positivity) (by linarith)
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [hh,hprod,hdR]
  calc
    (m*u+(C-m+1/3)/(2 : ℝ)^a)*Real.sqrt ((d : ℝ)+L)+
        Real.sqrt (1+(d : ℝ)/L) ≤ shortBudget d := by
      dsimp only [shortBudget]
      linarith only [hmain,htop]
    _ ≤ (2 : ℝ)^d := shortBudget_le d hd

end SymmetricSubgroupAsymptotics.BinaryAffineThreeComplementEnvelope
