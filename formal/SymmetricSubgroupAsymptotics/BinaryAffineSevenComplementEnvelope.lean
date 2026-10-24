import SymmetricSubgroupAsymptotics.BinaryAffineSevenComplementMargins

/-! A shared envelope for the entire complementary interval [7,15].
The exact Wallis square and the actual reciprocal complementary power
are retained together. The negative matching coefficient belongs to the
same total multiplicity, so replacing it by a dimension bound preserves
the joint chief-order charge. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineSevenComplementEnvelope
open BinaryAffineSevenComplementMargins

theorem matching_scaled_le (a d : ℕ) (hd : 1 ≤ d) (B v r : ℝ)
    (hB0 : 0 ≤ B) (hBv : 7*B ≤ v^2) (hv : 7 ≤ v) (hr : 0 ≤ r)
    (hwallis : r^2*(3*(a : ℝ)+2) ≤ 2) (hcap : r*v ≤ 1) :
    r*Real.sqrt ((d : ℝ)+(a : ℝ)+B) ≤ ((d : ℝ)+79)/88 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hv0 : 0 ≤ v := by linarith
  have hcap2 : r^2*v^2 ≤ 1 := by
    have hh := (sq_le_sq₀ (mul_nonneg hr hv0) (by norm_num : (0 : ℝ) ≤ 1)).mpr hcap
    simpa only [mul_pow,one_pow] using hh
  have hr7 : r ≤ 1/7 := by
    have hh := mul_le_mul_of_nonneg_left hv hr
    nlinarith only [hh,hcap]
  have hr2 : r^2 ≤ 1/49 := by
    have hh := (sq_le_sq₀ hr (by norm_num : (0 : ℝ) ≤ 1/7)).mpr hr7
    norm_num only [div_pow,one_pow] at hh
    exact hh
  have hB : 7*r^2*B ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hBv (sq_nonneg r)
    nlinarith only [hh,hcap2]
  have hrest := mul_le_mul_of_nonneg_right hr2
    (show 0 ≤ (d : ℝ)-2/3 by linarith)
  have hrad : r^2*((d : ℝ)+(a : ℝ)+B) ≤ ((d : ℝ)+39)/49 := by
    nlinarith only [hwallis,hB,hrest]
  have hN : 0 ≤ (d : ℝ)+(a : ℝ)+B := by positivity
  have hfirst : r*Real.sqrt ((d : ℝ)+(a : ℝ)+B) ≤ Real.sqrt ((d : ℝ)+39)/7 := by
    apply (sq_le_sq₀ (mul_nonneg hr (Real.sqrt_nonneg _)) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hN,div_pow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ)+39)]
    simpa only [show (7 : ℝ)^2 = 49 by norm_num] using hrad
  exact hfirst.trans (sqrt_ratio_le d hd)

theorem envelope_le (a d : ℕ) (ha : 6 ≤ a) (hd1 : 1 ≤ d) (hd6 : d ≤ 6)
    (C m B v r L : ℝ) (hm0 : 0 ≤ m) (hmC : m ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hmA : m ≤ (d : ℝ)*((d : ℝ)+1)/2)
    (hB0 : 0 ≤ B) (hB16 : B ≤ 16) (hBv : 7*B ≤ v^2) (hv : 7 ≤ v)
    (hr : 0 ≤ r) (hwallis : r^2*(3*(a : ℝ)+2) ≤ 2) (hcap : r*v ≤ 1)
    (hL8 : 8 ≤ L) (hLupper : L ≤ (a : ℝ)+B) :
    (m*r+(C-m+1/v)/(2 : ℝ)^a)*Real.sqrt ((d : ℝ)+L) +
      Real.sqrt (1+(d : ℝ)/L) ≤ (2 : ℝ)^d := by
  let k : ℝ := ((d : ℝ)+79)/88
  let A : ℝ := (d : ℝ)*((d : ℝ)+1)/2
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hdR6 : (d : ℝ) ≤ 6 := by exact_mod_cast hd6
  have hv0 : 0 < v := by linarith
  have hrad : (d : ℝ)+L ≤ (d : ℝ)+(a : ℝ)+B := by linarith only [hLupper]
  have hfirst : r*Real.sqrt ((d : ℝ)+L) ≤ k :=
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrad) hr).trans
      (matching_scaled_le a d hd1 B v r hB0 hBv hv hr hwallis hcap)
  have hrad22 : (d : ℝ)+L ≤ (a : ℝ)+22 := by linarith only [hLupper,hB16,hdR6]
  have herror : Real.sqrt ((d : ℝ)+L)/(2 : ℝ)^a ≤ 1/12 :=
    (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hrad22) (by positivity)).trans
      (primary_error_le a ha)
  have htop : Real.sqrt (1+(d : ℝ)/L) ≤ 1+(d : ℝ)/16 := by
    have hh := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ d by positivity)
      (by norm_num : (0 : ℝ) < 8) hL8
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith [sq_nonneg (d : ℝ)]
  have hi : 1/v ≤ (1/7 : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hv
  have hother : 0 ≤ C-m+1/v :=
    add_nonneg (sub_nonneg.mpr hmC) (div_nonneg (by norm_num) hv0.le)
  have hmain : (m*r+(C-m+1/v)/(2 : ℝ)^a)*Real.sqrt ((d : ℝ)+L) ≤
      A*k+((d : ℝ)^2-A+1/7)/12 := by
    have hprod := add_le_add (mul_le_mul_of_nonneg_left hfirst hm0)
      (mul_le_mul_of_nonneg_left herror hother)
    have hslope := mul_le_mul_of_nonneg_right hmA
      (show 0 ≤ k-1/12 by dsimp only [k]; linarith only [hdR])
    calc
      (m*r+(C-m+1/v)/(2 : ℝ)^a)*Real.sqrt ((d : ℝ)+L) =
          m*(r*Real.sqrt ((d : ℝ)+L))+
            (C-m+1/v)*(Real.sqrt ((d : ℝ)+L)/(2 : ℝ)^a) := by ring
      _ ≤ m*k+(C-m+1/v)/12 := by simpa only [div_eq_mul_inv,one_mul] using hprod
      _ ≤ A*k+((d : ℝ)^2-A+1/7)/12 := by
        change m*(k-1/12) ≤ A*(k-1/12) at hslope
        linarith only [hslope,hC,hi]
  calc
    (m*r+(C-m+1/v)/(2 : ℝ)^a)*Real.sqrt ((d : ℝ)+L)+
        Real.sqrt (1+(d : ℝ)/L) ≤ A*k+((d : ℝ)^2-A+1/7)/12+1+(d : ℝ)/16 := by
      linarith only [hmain,htop]
    _ = budget d := by dsimp only [A,k,budget]; ring
    _ ≤ (2 : ℝ)^d := budget_le d hd1

end SymmetricSubgroupAsymptotics.BinaryAffineSevenComplementEnvelope
