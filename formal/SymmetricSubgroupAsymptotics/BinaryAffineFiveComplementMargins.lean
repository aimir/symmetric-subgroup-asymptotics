import SymmetricSubgroupAsymptotics.ExactChoosePrimaryRateBounds

/-! Uniform margins for the complementary power five. The narrow
dimension-two margin is an exact rational inequality, and all larger
dimensions follow by a polynomial doubling induction. No dominant
exponent table or action census is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineFiveComplementMargins

def budget (d : ℕ) : ℝ :=
  ((d : ℝ)*((d : ℝ)+1)/2)*((d : ℝ)+45)/50 +
    ((d : ℝ)^2-(d : ℝ)*((d : ℝ)+1)/2+1/5)*(4*(d : ℝ)+89)/1792 +
      1+23*(d : ℝ)/400

theorem budget_le (d : ℕ) (hd : 2 ≤ d) : budget d ≤ (2 : ℝ)^d := by
  induction d,hd using Nat.le_induction with
  | base => norm_num [budget]
  | succ d hd ih =>
      have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
      have hx : 0 ≤ (d : ℝ)-2 := by linarith
      have heq : 2*budget d-budget (d+1) =
          249*((d : ℝ)-2)^3/22400+46329*((d : ℝ)-2)^2/89600+
            126981*((d : ℝ)-2)/89600+1987/2240 := by
        simp only [budget,Nat.cast_add,Nat.cast_one]
        ring
      have hnonneg : 0 ≤ 249*((d : ℝ)-2)^3/22400+46329*((d : ℝ)-2)^2/89600+
          126981*((d : ℝ)-2)/89600+1987/2240 := by positivity
      have hstep : budget (d+1) ≤ 2*budget d := by linarith only [heq,hnonneg]
      calc
        budget (d+1) ≤ 2*budget d := hstep
        _ ≤ 2*(2 : ℝ)^d := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ)^(d+1) := by rw [pow_succ]; ring

theorem dimension_one_margin :
    (46/50 : ℝ)+(1/5)*(93/1792)+17/16 ≤ 2 := by norm_num

theorem sqrt_ratio_le (d : ℕ) :
    Real.sqrt ((d : ℝ)+20)/5 ≤ ((d : ℝ)+45)/50 := by
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5)).mpr
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ)+20)]
  nlinarith only [sq_nonneg ((d : ℝ)-5)]

theorem primary_error_le (a d : ℕ) (ha : 6 ≤ a) :
    Real.sqrt ((a : ℝ)+(d : ℝ)+4)/(2 : ℝ)^a ≤ (4*(d : ℝ)+89)/1792 := by
  have hpow : (4096 : ℕ)*(a+d+4) ≤ 4^a*(d+10) := by
    induction a,ha using Nat.le_induction with
    | base =>
        norm_num only [show (4 : ℕ)^6 = 4096 by decide]
        omega
    | succ a ha ih =>
        have hstep : 4096*(a+1+d+4) ≤ 4*(4096*(a+d+4)) := by omega
        calc
          4096*(a+1+d+4) ≤ 4*(4096*(a+d+4)) := hstep
          _ ≤ 4*(4^a*(d+10)) := Nat.mul_le_mul_left 4 ih
          _ = 4^(a+1)*(d+10) := by rw [pow_succ]; ring
  have hpowR : (4096 : ℝ)*((a : ℝ)+(d : ℝ)+4) ≤ (4 : ℝ)^a*((d : ℝ)+10) := by
    exact_mod_cast hpow
  have hsq : ((2 : ℝ)^a)^2 = (4 : ℝ)^a := by
    rw [← pow_mul,mul_comm a 2,pow_mul]
    norm_num
  have hfirst : Real.sqrt ((a : ℝ)+(d : ℝ)+4)/(2 : ℝ)^a ≤
      Real.sqrt ((d : ℝ)+10)/64 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^a)).mpr
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (a : ℝ)+(d : ℝ)+4),mul_pow,
      div_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ)+10)]
    norm_num only [show (64 : ℝ)^2 = 4096 by norm_num]
    rw [hsq]
    nlinarith only [hpowR]
  have hroot : Real.sqrt ((d : ℝ)+10) ≤ (4*(d : ℝ)+89)/28 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ)+10)]
    nlinarith only [sq_nonneg (4*(d : ℝ)-9)]
  have hh := div_le_div_of_nonneg_right hroot (by norm_num : (0 : ℝ) ≤ 64)
  exact hfirst.trans (by convert hh using 1 <;> ring)

theorem top_ratio_le (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 33/4 ≤ L) :
    Real.sqrt (1+(d : ℝ)/L) ≤ 1+23*(d : ℝ)/400 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hh := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ d by positivity)
    (by norm_num : (0 : ℝ) < 33/4) hL
  have hprod : 0 ≤ (d : ℝ)*((d : ℝ)-2) := mul_nonneg (by positivity) (by linarith)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  nlinarith only [hh,hprod,hdR]

end SymmetricSubgroupAsymptotics.BinaryAffineFiveComplementMargins
