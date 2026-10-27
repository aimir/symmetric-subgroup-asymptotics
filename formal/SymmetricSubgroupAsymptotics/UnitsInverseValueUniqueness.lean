import Mathlib.Algebra.Group.Units.Defs

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics.UnitsInverseValueUniqueness

/-- A checked right inverse is the inverse value of the genuine unit. -/
theorem inverse_val_eq_of_mul_eq_one {A : Type*} [Monoid A]
    (a : Aˣ) (t : A) (h : (a : A) * t = 1) : ((a⁻¹ : Aˣ) : A) = t := by
  change a.inv = t
  calc
    a.inv = a.inv * 1 := (mul_one _).symm
    _ = a.inv * (a.val * t) := by rw [h]
    _ = t := by rw [← mul_assoc, a.inv_val, one_mul]

end SymmetricSubgroupAsymptotics.UnitsInverseValueUniqueness
