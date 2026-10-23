import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The actual singular-ray index estimate and a q^12 group-order
lower bound imply the strict least-index square, including q=3. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGGTwoIndexSquareNumerics

theorem index_square_lt (q ell order : ℕ) (hq : 3 ≤ q)
    (hell : ell < 3*q^5) (horder : q^12 ≤ order) : ell^2 < order := by
  have hq2 : 9 ≤ q^2 := by nlinarith
  calc
    ell^2 < (3*q^5)^2 := Nat.pow_lt_pow_left hell (by decide)
    _ = 9*q^10 := by ring
    _ ≤ q^2*q^10 := Nat.mul_le_mul_right _ hq2
    _ = q^12 := by ring
    _ ≤ order := horder

end SymmetricSubgroupAsymptotics.CFSGGTwoIndexSquareNumerics
