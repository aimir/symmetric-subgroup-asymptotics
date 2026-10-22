import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.LinearCombination

/-! The two literal parameters 1 and -1 recover both coefficients of a
quadratic root polynomial in odd characteristic. No exponential truncation
or characteristic-zero argument is used. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticParameterCentralizer
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem linear_coefficient (h2 : (2 : K) ≠ 0) (A X Y : Matrix I I K)
    (hp : A * (1 + X + Y) = (1 + X + Y) * A)
    (hm : A * (1 - X + Y) = (1 - X + Y) * A) : A * X = X * A := by
  ext i j
  have ep := congrArg (fun M : Matrix I I K => M i j) hp
  have em := congrArg (fun M : Matrix I I K => M i j) hm
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul,
    Matrix.add_apply, Matrix.sub_apply] at ep em
  apply mul_left_cancel₀ h2
  linear_combination ep - em

theorem quadratic_coefficient (h2 : (2 : K) ≠ 0) (A X Y : Matrix I I K)
    (hp : A * (1 + X + Y) = (1 + X + Y) * A)
    (hm : A * (1 - X + Y) = (1 - X + Y) * A) : A * Y = Y * A := by
  have hX := linear_coefficient h2 A X Y hp hm
  simp only [mul_add, add_mul, mul_one, one_mul, hX] at hp
  exact add_left_cancel hp

end SymmetricSubgroupAsymptotics.CFSGQuadraticParameterCentralizer
