import SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeRemainderNumerics

/-! Three uniform exponential margins for the complementary-divisor
interval [16,M]. These are polynomial inductions in the affine dimension,
not tables of actions, dimensions, exponents or fitted scalar premises. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineComplementaryLargeIntervalMargins

def smallBudget (d : ℕ) : ℝ :=
  (3*((d : ℝ)*((d : ℝ)+1)/2)+(d : ℝ)^2+1)*((d : ℝ)+162)/1152+1+(d : ℝ)/12

def binaryBudget (d : ℕ) : ℝ :=
  (63*((d : ℝ)*((d : ℝ)+1)/2)+(d : ℝ)^2+1)*((d : ℝ)+392)/28672+1+(d : ℝ)/20

def oddBudget (d : ℕ) : ℝ :=
  (63*((d : ℝ)-1)+(d : ℝ)^2+1)*((d : ℝ)+1458)/55296+1+(d : ℝ)/20

theorem smallBudget_le (d : ℕ) (hd : 1 ≤ d) : smallBudget d ≤ (2 : ℝ)^d := by
  induction d,hd using Nat.le_induction with
  | base => norm_num [smallBudget]
  | succ d hd ih =>
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hx : 0 ≤ (d : ℝ)-1 := by linarith
      have heq : 2*smallBudget d-smallBudget (d+1) =
          (5*((d : ℝ)-1)^3+813*((d : ℝ)-1)^2+650*((d : ℝ)-1)+972)/2304 := by
        simp only [smallBudget,Nat.cast_add,Nat.cast_one]
        ring
      have hstep : smallBudget (d+1) ≤ 2*smallBudget d := by
        have hnonneg : 0 ≤
            (5*((d : ℝ)-1)^3+813*((d : ℝ)-1)^2+650*((d : ℝ)-1)+972)/2304 := by
          positivity
        linarith only [heq,hnonneg]
      calc
        smallBudget (d+1) ≤ 2*smallBudget d := hstep
        _ ≤ 2*(2 : ℝ)^d := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ)^(d+1) := by rw [pow_succ]; ring

theorem binaryBudget_le (d : ℕ) (hd : 1 ≤ d) : binaryBudget d ≤ (2 : ℝ)^d := by
  induction d,hd using Nat.le_induction with
  | base => norm_num [binaryBudget]
  | succ d hd ih =>
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hx : 0 ≤ (d : ℝ)-1 := by linarith
      have heq : 2*binaryBudget d-binaryBudget (d+1) =
          (325*((d : ℝ)-1)^3+127715*((d : ℝ)-1)^2+
            135876*((d : ℝ)-1)+33260)/286720 := by
        simp only [binaryBudget,Nat.cast_add,Nat.cast_one]
        ring
      have hstep : binaryBudget (d+1) ≤ 2*binaryBudget d := by
        have hnonneg : 0 ≤
            (325*((d : ℝ)-1)^3+127715*((d : ℝ)-1)^2+
              135876*((d : ℝ)-1)+33260)/286720 := by
          positivity
        linarith only [heq,hnonneg]
      calc
        binaryBudget (d+1) ≤ 2*binaryBudget d := hstep
        _ ≤ 2*(2 : ℝ)^d := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ)^(d+1) := by rw [pow_succ]; ring

private theorem oddBudget_le_two (d : ℕ) (hd : 2 ≤ d) : oddBudget d ≤ (2 : ℝ)^d := by
  induction d,hd using Nat.le_induction with
  | base => norm_num [oddBudget]
  | succ d hd ih =>
      have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
      have hx : 0 ≤ (d : ℝ)-2 := by linarith
      have heq : 2*oddBudget d-oddBudget (d+1) =
          (5*((d : ℝ)-2)^3+7620*((d : ℝ)-2)^2+
            487979*((d : ℝ)-2)+289624)/276480 := by
        simp only [oddBudget,Nat.cast_add,Nat.cast_one]
        ring
      have hstep : oddBudget (d+1) ≤ 2*oddBudget d := by
        have hnonneg : 0 ≤
            (5*((d : ℝ)-2)^3+7620*((d : ℝ)-2)^2+
              487979*((d : ℝ)-2)+289624)/276480 := by
          positivity
        linarith only [heq,hnonneg]
      calc
        oddBudget (d+1) ≤ 2*oddBudget d := hstep
        _ ≤ 2*(2 : ℝ)^d := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ)^(d+1) := by rw [pow_succ]; ring

theorem oddBudget_le (d : ℕ) (hd : 1 ≤ d) : oddBudget d ≤ (2 : ℝ)^d := by
  by_cases hd1 : d = 1
  · subst d
    norm_num [oddBudget]
  · exact oddBudget_le_two d (by omega)

end SymmetricSubgroupAsymptotics.BinaryAffineComplementaryLargeIntervalMargins
