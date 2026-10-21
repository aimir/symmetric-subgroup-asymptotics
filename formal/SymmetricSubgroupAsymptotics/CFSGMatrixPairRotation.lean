import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Abel

/-! A quarter-turn on one actual coordinate pair, identity elsewhere.
The sparse identities are uniform in the index type and coefficient
characteristic. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGMatrixPairRotation
variable (R : Type*) [CommRing R] {I : Type*} [Fintype I] [DecidableEq I]

def projection (p q : I) : Matrix I I R := Matrix.single p p 1 + Matrix.single q q 1

def rotation (p q : I) : Matrix I I R :=
  1 - Matrix.single p p 1 - Matrix.single q q 1 - Matrix.single p q 1 + Matrix.single q p 1

theorem projection_sq (p q : I) (hpq : p ≠ q) :
    projection R p q * projection R p q = projection R p q := by
  simp [projection, add_mul, mul_add, hpq, Ne.symm hpq]

theorem word_eq_rotation (p q : I) (hpq : p ≠ q) :
    (1 - Matrix.single p q (1 : R)) * (1 + Matrix.single q p 1) *
      (1 - Matrix.single p q 1) = rotation R p q := by
  simp [rotation, sub_mul, mul_sub, add_mul, mul_add, hpq, Ne.symm hpq] <;> abel

theorem rotation_sq (p q : I) (hpq : p ≠ q) :
    rotation R p q ^ 2 = 1 - projection R p q - projection R p q := by
  simp [rotation, projection, pow_two, sub_mul, mul_sub, add_mul, mul_add,
    hpq, Ne.symm hpq] <;> abel

theorem reflection_sq (P : Matrix I I R) (hP : P * P = P) : (1 - P - P) ^ 2 = 1 := by
  simp [pow_two, sub_mul, mul_sub, hP] <;> abel

theorem rotation_four (p q : I) (hpq : p ≠ q) : rotation R p q ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, rotation_sq R p q hpq]
  exact reflection_sq R _ (projection_sq R p q hpq)

theorem rotation_entry (p q : I) (hpq : p ≠ q) : rotation R p q q p = 1 := by
  simp [rotation, Matrix.single, Matrix.one_apply, hpq, Ne.symm hpq]

end SymmetricSubgroupAsymptotics.CFSGMatrixPairRotation
