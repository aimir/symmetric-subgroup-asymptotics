import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring

/-! Scalar identities for the transpose quadratic form of the actual
characteristic-two B matrices. These are symbolic finite-sum identities,
with no enumeration of vectors or generated groups. -/
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationQuadraticShears
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem chain_shear (x y : I → K) (a b : I) (hab : a ≠ b) (t : K) :
    (∑ j, (x j + if j = b then t * x a else 0) *
      (y j - if j = a then t * y b else 0)) = ∑ j, x j * y j := by
  have ht (j : I) :
      (x j + if j = b then t * x a else 0) *
        (y j - if j = a then t * y b else 0) =
      x j * y j + (if j = b then t * x a * y b else 0) -
        (if j = a then t * x a * y b else 0) := by
    by_cases ha : j = a <;> by_cases hb : j = b <;> simp_all <;> ring
  simp_rw [ht]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp

theorem short_shear_second [CharP K 2] (x y : I → K) (z : K) (a : I) (t : K) :
    (∑ j, x j * (y j - if j = a then t ^ 2 * x a else 0)) + (z + t * x a) ^ 2 =
      (∑ j, x j * y j) + z ^ 2 := by
  have ht (j : I) : x j * (y j - if j = a then t ^ 2 * x a else 0) =
      x j * y j - if j = a then t ^ 2 * (x a) ^ 2 else 0 := by
    by_cases h : j = a <;> simp [h] <;> ring
  simp_rw [ht]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [CharTwo.add_sq, mul_pow]
  ring

theorem short_shear_first [CharP K 2] (x y : I → K) (z : K) (a : I) (t : K) :
    (∑ j, (x j - if j = a then t ^ 2 * y a else 0) * y j) + (z - t * y a) ^ 2 =
      (∑ j, x j * y j) + z ^ 2 := by
  have hh := short_shear_second y x z a t
  simpa only [mul_comm, sub_eq_add_neg, CharTwo.neg_eq] using hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationQuadraticShears
