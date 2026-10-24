import SymmetricSubgroupAsymptotics.ExactChoosePrimaryRateBounds

/-! Two uniform dimension ranges for complementary power three.
The small dimension-two exponents are handled by the separate actual
shared-head theorem. These scalar budgets are polynomial inductions,
and the root-ratio comparison is valid for every larger exponent. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineThreeComplementMargins

def largeBudget (d : ℕ) : ℝ :=
  ((d : ℝ)*((d : ℝ)+1)/2)*((d : ℝ)+18)/20 +
    ((d : ℝ)^2-(d : ℝ)*((d : ℝ)+1)/2+1/3)*((d : ℝ)+11)/256+1+(d : ℝ)/15

def shortBudget (d : ℕ) : ℝ :=
  ((d : ℝ)*((d : ℝ)+1)/2)*((d : ℝ)+22)/25 +
    ((d : ℝ)^2-(d : ℝ)*((d : ℝ)+1)/2+1/3)*((d : ℝ)+12)/1024+1+251*(d : ℝ)/5000

theorem largeBudget_le (d : ℕ) (hd : 3 ≤ d) : largeBudget d ≤ (2 : ℝ)^d := by
  induction d,hd using Nat.le_induction with
  | base => norm_num [largeBudget]
  | succ d hd ih =>
      have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
      have hx : 0 ≤ (d : ℝ)-3 := by linarith
      have heq : 2*largeBudget d-largeBudget (d+1) =
          69*((d : ℝ)-3)^3/2560+21*((d : ℝ)-3)^2/32+
            6749*((d : ℝ)-3)/2560+10471/3840 := by
        simp only [largeBudget,Nat.cast_add,Nat.cast_one]
        ring
      have hnonneg : 0 ≤ 69*((d : ℝ)-3)^3/2560+21*((d : ℝ)-3)^2/32+
          6749*((d : ℝ)-3)/2560+10471/3840 := by positivity
      have hstep : largeBudget (d+1) ≤ 2*largeBudget d := by linarith only [heq,hnonneg]
      calc
        largeBudget (d+1) ≤ 2*largeBudget d := hstep
        _ ≤ 2*(2 : ℝ)^d := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ)^(d+1) := by rw [pow_succ]; ring

theorem shortBudget_le (d : ℕ) (hd : 2 ≤ d) : shortBudget d ≤ (2 : ℝ)^d := by
  induction d,hd using Nat.le_induction with
  | base => norm_num [shortBudget]
  | succ d hd ih =>
      have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
      have hx : 0 ≤ (d : ℝ)-2 := by linarith
      have heq : 2*shortBudget d-shortBudget (d+1) =
          1049*((d : ℝ)-2)^3/51200+13487*((d : ℝ)-2)^2/25600+
            5199143*((d : ℝ)-2)/3840000+765917/960000 := by
        simp only [shortBudget,Nat.cast_add,Nat.cast_one]
        ring
      have hnonneg : 0 ≤ 1049*((d : ℝ)-2)^3/51200+13487*((d : ℝ)-2)^2/25600+
          5199143*((d : ℝ)-2)/3840000+765917/960000 := by positivity
      have hstep : shortBudget (d+1) ≤ 2*shortBudget d := by linarith only [heq,hnonneg]
      calc
        shortBudget (d+1) ≤ 2*shortBudget d := hstep
        _ ≤ 2*(2 : ℝ)^d := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ)^(d+1) := by rw [pow_succ]; ring

theorem shifted_error_antitone (k a d : ℕ) (hk : 1 ≤ k) (hka : k ≤ a) (hd : 1 ≤ d) :
    Real.sqrt ((a : ℝ)+(d : ℝ)+8/5)/(2 : ℝ)^a ≤
      Real.sqrt ((k : ℝ)+(d : ℝ)+8/5)/(2 : ℝ)^k := by
  induction a,hka using Nat.le_induction with
  | base => exact le_rfl
  | succ a ha ih =>
      have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (hk.trans ha)
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hroot : Real.sqrt (((a+1 : ℕ) : ℝ)+(d : ℝ)+8/5) ≤
          2*Real.sqrt ((a : ℝ)+(d : ℝ)+8/5) := by
        apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
        rw [mul_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (a : ℝ)+(d : ℝ)+8/5),
          Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((a+1 : ℕ) : ℝ)+(d : ℝ)+8/5)]
        push_cast
        nlinarith only [ha1,hd1]
      calc
        Real.sqrt (((a+1 : ℕ) : ℝ)+(d : ℝ)+8/5)/(2 : ℝ)^(a+1) ≤
            (2*Real.sqrt ((a : ℝ)+(d : ℝ)+8/5))/(2 : ℝ)^(a+1) :=
          div_le_div_of_nonneg_right hroot (by positivity)
        _ = Real.sqrt ((a : ℝ)+(d : ℝ)+8/5)/(2 : ℝ)^a := by
          rw [pow_succ]
          field_simp <;> ring
        _ ≤ Real.sqrt ((k : ℝ)+(d : ℝ)+8/5)/(2 : ℝ)^k := ih

end SymmetricSubgroupAsymptotics.BinaryAffineThreeComplementMargins
