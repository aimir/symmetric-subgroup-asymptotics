import SymmetricSubgroupAsymptotics.CFSGIntegralSquareZeroOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-! Integral square-zero adjoint exponentials are actual conjugations
by transvections in every characteristic. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSquareZeroConjugation
open scoped BigOperators
variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B]

theorem transvection_mul_inverse (t : R) (e : B) (he : e * e = 0) :
    (1 + t • e) * (1 - t • e) = 1 := by
  have hs : (t • e) * (t • e) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, he, smul_zero]
  calc
    (1 + t • e) * (1 - t • e) = (1 + t • e) - (t • e + (t • e) * (t • e)) := by
      rw [mul_sub, mul_one, add_mul, one_mul]
    _ = 1 := by rw [hs, add_zero, add_sub_cancel_right]

theorem inverse_mul_transvection (t : R) (e : B) (he : e * e = 0) :
    (1 - t • e) * (1 + t • e) = 1 := by
  have hs : (t • e) * (t • e) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, he, smul_zero]
  calc
    (1 - t • e) * (1 + t • e) = (1 - t • e) + (t • e - (t • e) * (t • e)) := by
      rw [mul_add, mul_one, sub_mul, one_mul]
    _ = 1 := by rw [hs, sub_zero, sub_add_cancel]

theorem polynomial_eq_conjugation (t : R) (e x : B) :
    x + t • (e * x - x * e) - t ^ 2 • (e * x * e) =
      (1 + t • e) * x * (1 - t • e) := by
  simp only [add_mul, mul_sub, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_sub, smul_add, smul_neg, smul_smul, pow_two, mul_assoc]
  abel

theorem operator_sum_eq_conjugation (t : R) (e x : B) :
    (∑ k ∈ Finset.range 4,
      t ^ k • CFSGIntegralSquareZeroOperators.operator R e k x) =
      (1 + t • e) * x * (1 - t • e) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    CFSGIntegralSquareZeroOperators.operator_zero,
    CFSGIntegralSquareZeroOperators.operator_one,
    CFSGIntegralSquareZeroOperators.operator_two,
    CFSGIntegralSquareZeroOperators.operator_large R e x 3 (by decide),
    pow_zero, pow_one, one_smul, smul_zero, add_zero, smul_neg]
  simpa only [sub_eq_add_neg] using polynomial_eq_conjugation t e x

end SymmetricSubgroupAsymptotics.CFSGSquareZeroConjugation
