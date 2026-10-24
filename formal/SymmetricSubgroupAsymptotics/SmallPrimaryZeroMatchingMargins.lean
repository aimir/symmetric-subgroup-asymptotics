import SymmetricSubgroupAsymptotics.BinaryAffineSevenComplementMargins

/-! One dimension-uniform zero-matching margin on small primary powers
at least eleven. This is a polynomial induction and a monotone primary
denominator comparison, not a list of affine dimensions or top degrees. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallPrimaryZeroMatchingMargins

def budget (d : ℕ) : ℝ := ((d : ℝ)^2+1)*((d : ℝ)+20)/55+1+(d : ℝ)/6

theorem budget_le (d : ℕ) (hd : 1 ≤ d) : budget d ≤ (2 : ℝ)^d := by
  induction d,hd using Nat.le_induction with
  | base => norm_num [budget]
  | succ d hd ih =>
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hx : 0 ≤ (d : ℝ)-1 := by linarith
      have heq : 2*budget d-budget (d+1) =
          ((d : ℝ)-1)^3/55+4*((d : ℝ)-1)^2/11+
            5*((d : ℝ)-1)/66+29/55 := by
        simp only [budget,Nat.cast_add,Nat.cast_one]
        ring
      have hnonneg : 0 ≤ ((d : ℝ)-1)^3/55+4*((d : ℝ)-1)^2/11+
          5*((d : ℝ)-1)/66+29/55 := by positivity
      have hstep : budget (d+1) ≤ 2*budget d := by linarith only [heq,hnonneg]
      calc
        budget (d+1) ≤ 2*budget d := hstep
        _ ≤ 2*(2 : ℝ)^d := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ)^(d+1) := by rw [pow_succ]; ring

theorem root_div_le (M d : ℕ) (hM : 11 ≤ M) (hd : 1 ≤ d) :
    Real.sqrt ((d : ℝ)+(3/2)*(M : ℝ))/(M : ℝ) ≤ ((d : ℝ)+20)/55 := by
  have hMR : (11 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hMsq : (121 : ℝ) ≤ (M : ℝ)^2 := by nlinarith only [sq_nonneg ((M : ℝ)-11),hMR]
  have hD : 0 ≤ (d : ℝ)*((M : ℝ)^2-121) :=
    mul_nonneg (by positivity) (by linarith only [hMsq])
  have hsub : 0 ≤ (M : ℝ)-11 := by linarith only [hMR]
  have hP : 0 ≤ (33/2 : ℝ)*(M : ℝ)*((M : ℝ)-11) := by positivity
  have hfrac : ((d : ℝ)+(3/2)*(M : ℝ))/(M : ℝ)^2 ≤ ((d : ℝ)+33/2)/121 := by
    apply (div_le_iff₀ (pow_pos hM0 2)).mpr
    nlinarith only [hD,hP]
  apply (sq_le_sq₀ (div_nonneg (Real.sqrt_nonneg _) hM0.le) (by positivity)).mp
  rw [div_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ)+(3/2)*(M : ℝ))]
  have hlast : ((d : ℝ)+33/2)/121 ≤ (((d : ℝ)+20)/55)^2 := by
    nlinarith only [sq_nonneg (d : ℝ),hdR]
  exact hfrac.trans hlast

end SymmetricSubgroupAsymptotics.SmallPrimaryZeroMatchingMargins
