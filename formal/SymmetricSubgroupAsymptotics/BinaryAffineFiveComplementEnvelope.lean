import SymmetricSubgroupAsymptotics.BinaryAffineFiveComplementMargins

/-! Uniform exact-choose envelope for complementary power five. The
binary primary exponent is unrestricted above five. The total and
matching coefficients retain their common chief-order charge. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineFiveComplementEnvelope
open BinaryAffineFiveComplementMargins

theorem matching_scaled_le (a d : ℕ) (hd : 1 ≤ d) (B r : ℝ)
    (hB0 : 0 ≤ B) (hB4 : B ≤ 4) (hr : 0 ≤ r)
    (hwallis : r^2*(3*(a : ℝ)+2) ≤ 2) (hcap : 5*r ≤ 1) :
    r*Real.sqrt ((d : ℝ)+(a : ℝ)+B) ≤ ((d : ℝ)+45)/50 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr5 : r ≤ 1/5 := by linarith only [hcap]
  have hr2 : r^2 ≤ 1/25 := by
    have hh := (sq_le_sq₀ hr (by norm_num : (0 : ℝ) ≤ 1/5)).mpr hr5
    norm_num only [div_pow,one_pow] at hh
    exact hh
  have hB := mul_le_mul_of_nonneg_left hB4 (sq_nonneg r)
  have hrest := mul_le_mul_of_nonneg_right hr2
    (show 0 ≤ (d : ℝ)+4-2/3 by linarith)
  have hrad : r^2*((d : ℝ)+(a : ℝ)+B) ≤ ((d : ℝ)+20)/25 := by
    nlinarith only [hwallis,hB,hrest]
  have hN : 0 ≤ (d : ℝ)+(a : ℝ)+B := by positivity
  have hfirst : r*Real.sqrt ((d : ℝ)+(a : ℝ)+B) ≤ Real.sqrt ((d : ℝ)+20)/5 := by
    apply (sq_le_sq₀ (mul_nonneg hr (Real.sqrt_nonneg _)) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hN,div_pow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ)+20)]
    simpa only [show (5 : ℝ)^2 = 25 by norm_num] using hrad
  exact hfirst.trans (sqrt_ratio_le d)

theorem envelope_le (a d : ℕ) (ha : 6 ≤ a) (hd1 : 1 ≤ d)
    (C m B r L : ℝ) (hm0 : 0 ≤ m) (hmC : m ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hmA : m ≤ (d : ℝ)*((d : ℝ)+1)/2)
    (hB0 : 0 ≤ B) (hB4 : B ≤ 4) (hr : 0 ≤ r)
    (hwallis : r^2*(3*(a : ℝ)+2) ≤ 2) (hcap : 5*r ≤ 1)
    (hL : 33/4 ≤ L) (hLupper : L ≤ (a : ℝ)+B) :
    (m*r+(C-m+1/5)/(2 : ℝ)^a)*Real.sqrt ((d : ℝ)+L) +
      Real.sqrt (1+(d : ℝ)/L) ≤ (2 : ℝ)^d := by
  let k : ℝ := ((d : ℝ)+45)/50
  let y : ℝ := (4*(d : ℝ)+89)/1792
  let A : ℝ := (d : ℝ)*((d : ℝ)+1)/2
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hrad : (d : ℝ)+L ≤ (d : ℝ)+(a : ℝ)+B := by linarith only [hLupper]
  have hfirst : r*Real.sqrt ((d : ℝ)+L) ≤ k :=
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrad) hr).trans
      (matching_scaled_le a d hd1 B r hB0 hB4 hr hwallis hcap)
  have hrad4 : (d : ℝ)+L ≤ (a : ℝ)+(d : ℝ)+4 := by linarith only [hLupper,hB4]
  have herror : Real.sqrt ((d : ℝ)+L)/(2 : ℝ)^a ≤ y :=
    (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hrad4) (by positivity)).trans
      (primary_error_le a d ha)
  have hother : 0 ≤ C-m+1/5 := by linarith only [hmC]
  have hmain : (m*r+(C-m+1/5)/(2 : ℝ)^a)*Real.sqrt ((d : ℝ)+L) ≤
      A*k+((d : ℝ)^2-A+1/5)*y := by
    have hprod := add_le_add (mul_le_mul_of_nonneg_left hfirst hm0)
      (mul_le_mul_of_nonneg_left herror hother)
    have hslope := mul_le_mul_of_nonneg_right hmA
      (show 0 ≤ k-y by dsimp only [k,y]; linarith only [hdR])
    calc
      (m*r+(C-m+1/5)/(2 : ℝ)^a)*Real.sqrt ((d : ℝ)+L) =
          m*(r*Real.sqrt ((d : ℝ)+L))+
            (C-m+1/5)*(Real.sqrt ((d : ℝ)+L)/(2 : ℝ)^a) := by ring
      _ ≤ m*k+(C-m+1/5)*y := hprod
      _ ≤ A*k+((d : ℝ)^2-A+1/5)*y := by
        change m*(k-y) ≤ A*(k-y) at hslope
        have hy : 0 ≤ y := by dsimp only [y]; positivity
        have hh := mul_le_mul_of_nonneg_right hC hy
        linarith only [hslope,hh]
  by_cases hd : d = 1
  · have htop : Real.sqrt (1+(d : ℝ)/L) ≤ 17/16 := by
      have hh := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ d by positivity)
        (by norm_num : (0 : ℝ) < 33/4) hL
      apply Real.sqrt_le_iff.mpr
      refine ⟨by norm_num,?_⟩
      rw [hd] at hh ⊢
      norm_num at hh ⊢
      linarith only [hh]
    calc
      (m*r+(C-m+1/5)/(2 : ℝ)^a)*Real.sqrt ((d : ℝ)+L)+
          Real.sqrt (1+(d : ℝ)/L) ≤ A*k+((d : ℝ)^2-A+1/5)*y+17/16 :=
        add_le_add hmain htop
      _ ≤ (2 : ℝ)^d := by
        norm_num [A,k,y,hd]
  · have hd2 : 2 ≤ d := by omega
    have htop := top_ratio_le d hd2 L hL
    calc
      (m*r+(C-m+1/5)/(2 : ℝ)^a)*Real.sqrt ((d : ℝ)+L)+
          Real.sqrt (1+(d : ℝ)/L) ≤ A*k+((d : ℝ)^2-A+1/5)*y+1+23*(d : ℝ)/400 := by
        linarith only [hmain,htop]
      _ = budget d := by dsimp only [A,k,y,budget]; ring
      _ ≤ (2 : ℝ)^d := budget_le d hd2

end SymmetricSubgroupAsymptotics.BinaryAffineFiveComplementEnvelope
