import SymmetricSubgroupAsymptotics.ExactChoosePrimaryRateBounds

/-! Uniform margins for binary dominant powers with complementary
prime powers at least seven. The dimension estimate is a polynomial
induction, not a list of dimensions or exponents. Actual complementary
entropy and the original action are supplied by separate consumers. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineSevenComplementMargins

def budget (d : ℕ) : ℝ :=
  ((d : ℝ)*((d : ℝ)+1)/2)*((d : ℝ)+79)/88 +
    ((d : ℝ)^2-(d : ℝ)*((d : ℝ)+1)/2+1/7)/12 + 1+(d : ℝ)/16

private theorem budget_le_two (d : ℕ) (hd : 2 ≤ d) : budget d ≤ (2 : ℝ)^d := by
  induction d,hd using Nat.le_induction with
  | base => norm_num [budget]
  | succ d hd ih =>
      have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
      have hx : 0 ≤ (d : ℝ)-2 := by linarith
      have heq : 2*budget d-budget (d+1) =
          ((d : ℝ)-2)^3/176+271*((d : ℝ)-2)^2/528+
            763*((d : ℝ)-2)/528+1137/1232 := by
        simp only [budget,Nat.cast_add,Nat.cast_one]
        ring
      have hnonneg : 0 ≤ ((d : ℝ)-2)^3/176+271*((d : ℝ)-2)^2/528+
          763*((d : ℝ)-2)/528+1137/1232 := by positivity
      have hstep : budget (d+1) ≤ 2*budget d := by linarith only [heq,hnonneg]
      calc
        budget (d+1) ≤ 2*budget d := hstep
        _ ≤ 2*(2 : ℝ)^d := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ)^(d+1) := by rw [pow_succ]; ring

theorem budget_le (d : ℕ) (hd : 1 ≤ d) : budget d ≤ (2 : ℝ)^d := by
  by_cases h1 : d = 1
  · subst d
    norm_num [budget]
  · exact budget_le_two d (by omega)

theorem sqrt_ratio_le (d : ℕ) (hd : 1 ≤ d) :
    Real.sqrt ((d : ℝ)+39)/7 ≤ ((d : ℝ)+79)/88 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 7)).mpr
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ)+39)]
  nlinarith only [sq_nonneg ((d : ℝ)-1),hdR]

theorem primary_error_le (a : ℕ) (ha : 6 ≤ a) :
    Real.sqrt ((a : ℝ)+22)/(2 : ℝ)^a ≤ 1/12 := by
  have hpow : (144 : ℕ)*(a+22) ≤ 4^a := by
    induction a,ha using Nat.le_induction with
    | base => norm_num
    | succ a ha ih =>
        have hstep : 144*(a+1+22) ≤ 4*(144*(a+22)) := by omega
        calc
          144*(a+1+22) ≤ 4*(144*(a+22)) := hstep
          _ ≤ 4*4^a := Nat.mul_le_mul_left 4 ih
          _ = 4^(a+1) := by rw [pow_succ]; omega
  have hpowR : (144 : ℝ)*((a : ℝ)+22) ≤ (4 : ℝ)^a := by exact_mod_cast hpow
  have hsq : ((2 : ℝ)^a)^2 = (4 : ℝ)^a := by rw [← pow_mul, mul_comm a 2, pow_mul]; norm_num
  have hsqrt : Real.sqrt ((a : ℝ)+22) ≤ (2 : ℝ)^a/12 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (a : ℝ)+22)]
    nlinarith only [hpowR,hsq]
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^a)).mpr (by linarith)

end SymmetricSubgroupAsymptotics.BinaryAffineSevenComplementMargins
