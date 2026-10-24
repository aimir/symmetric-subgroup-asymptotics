import SymmetricSubgroupAsymptotics.TinyComplementOddMargins

/-! Uniform higher-dimensional tiny-complement budgets. These scalar
inequalities use induction in every dimension at least four. They retain
the separate binary shared-divisor cost and the actual three/six-point
ternary shapes; no action catalogue or assumed scalar fitting is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TinyComplementHigherPolynomialBudgets

def binary (d : ℕ) : ℝ := ((7*(d : ℝ)^2/24+(d : ℝ)/24-5/12)*(10*(d : ℝ)+91)/40+((d : ℝ)+11)/10)

theorem binary_le (d : ℕ) (hd : 4 ≤ d) : binary d ≤ (2 : ℝ)^d := by
  induction d,hd using Nat.le_induction with
  | base => norm_num [binary]
  | succ d hd ih =>
      have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
      have hx : 0 ≤ (d : ℝ)-4 := by linarith only [hdR]
      have heq : 2*binary d-binary (d+1) =
          7*((d : ℝ)-4)^3/96+1277*((d : ℝ)-4)^2/960+1813*((d : ℝ)-4)/320+2573/480 := by
        simp only [binary,Nat.cast_add,Nat.cast_one]
        ring
      have hnonneg : 0 ≤ 7*((d : ℝ)-4)^3/96+1277*((d : ℝ)-4)^2/960+1813*((d : ℝ)-4)/320+2573/480 := by positivity
      have hstep : binary (d+1) ≤ 2*binary d := by linarith only [heq,hnonneg]
      calc
        binary (d+1) ≤ 2*binary d := hstep
        _ ≤ 2*((2 : ℝ)^d) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ)^(d+1) := by rw [pow_succ]; ring

def ternaryThree (d : ℕ) : ℝ := (((d : ℝ)^2+(d : ℝ)/2)*((d : ℝ)+6)/4)

theorem ternaryThree_le (d : ℕ) (hd : 4 ≤ d) : ternaryThree d ≤ 3*(2 : ℝ)^d := by
  induction d,hd using Nat.le_induction with
  | base => norm_num [ternaryThree]
  | succ d hd ih =>
      have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
      have hx : 0 ≤ (d : ℝ)-4 := by linarith only [hdR]
      have heq : 2*ternaryThree d-ternaryThree (d+1) =
          ((d : ℝ)-4)^3/4+31*((d : ℝ)-4)^2/8+63*((d : ℝ)-4)/4+115/8 := by
        simp only [ternaryThree,Nat.cast_add,Nat.cast_one]
        ring
      have hnonneg : 0 ≤ ((d : ℝ)-4)^3/4+31*((d : ℝ)-4)^2/8+63*((d : ℝ)-4)/4+115/8 := by positivity
      have hstep : ternaryThree (d+1) ≤ 2*ternaryThree d := by linarith only [heq,hnonneg]
      calc
        ternaryThree (d+1) ≤ 2*ternaryThree d := hstep
        _ ≤ 2*(3*(2 : ℝ)^d) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = 3*(2 : ℝ)^(d+1) := by rw [pow_succ]; ring

def ternarySix (d : ℕ) : ℝ := ((2*(d : ℝ)^2+(d : ℝ)-2)*((d : ℝ)+7)/4)

theorem ternarySix_le (d : ℕ) (hd : 4 ≤ d) : ternarySix d ≤ 6*(2 : ℝ)^d := by
  induction d,hd using Nat.le_induction with
  | base => norm_num [ternarySix]
  | succ d hd ih =>
      have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
      have hx : 0 ≤ (d : ℝ)-4 := by linarith only [hdR]
      have heq : 2*ternarySix d-ternarySix (d+1) =
          ((d : ℝ)-4)^3/2+33*((d : ℝ)-4)^2/4+137*((d : ℝ)-4)/4+28 := by
        simp only [ternarySix,Nat.cast_add,Nat.cast_one]
        ring
      have hnonneg : 0 ≤ ((d : ℝ)-4)^3/2+33*((d : ℝ)-4)^2/4+137*((d : ℝ)-4)/4+28 := by positivity
      have hstep : ternarySix (d+1) ≤ 2*ternarySix d := by linarith only [heq,hnonneg]
      calc
        ternarySix (d+1) ≤ 2*ternarySix d := hstep
        _ ≤ 2*(6*(2 : ℝ)^d) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = 6*(2 : ℝ)^(d+1) := by rw [pow_succ]; ring

end SymmetricSubgroupAsymptotics.TinyComplementHigherPolynomialBudgets
