import SymmetricSubgroupAsymptotics.CFSGSquareZeroDividedPowers
import Mathlib.Algebra.Module.LinearMap.Basic

/-! The divided adjoint powers of a square-zero root have integral
polynomial formulas. These formulas make sense in every characteristic. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGIntegralSquareZeroOperators
variable (R : Type*) [CommRing R] {B : Type*} [Ring B] [Algebra R B]

def operator (e : B) (k : ℕ) : Module.End R B :=
  if k = 0 then 1 else if k = 1 then
    LinearMap.mulLeft R e - LinearMap.mulRight R e else if k = 2 then
    -((LinearMap.mulRight R e).comp (LinearMap.mulLeft R e)) else 0

@[simp] theorem operator_zero (e x : B) : operator R e 0 x = x := by
  simp [operator]

@[simp] theorem operator_one (e x : B) : operator R e 1 x = e * x - x * e := by
  simp [operator]

@[simp] theorem operator_two (e x : B) : operator R e 2 x = -(e * x * e) := by
  simp [operator]

theorem operator_large (e x : B) (k : ℕ) (hk : 3 ≤ k) : operator R e k x = 0 := by
  simp [operator, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]

theorem operator_changeScalars (S : Type*) [CommRing S] [Algebra S B]
    (e x : B) (k : ℕ) : operator R e k x = operator S e k x := by
  unfold operator
  split_ifs <;> rfl

theorem map_operator {C : Type*} [Ring C] [Algebra R C]
    (f : B →+* C) (e x : B) (k : ℕ) :
    f (operator R e k x) = operator R (f e) k (f x) := by
  by_cases hk : 3 ≤ k
  · rw [operator_large R e x k hk, map_zero, operator_large R (f e) (f x) k hk]
  · have hlt : k < 3 := by omega
    interval_cases k <;> simp only [operator_zero, operator_one, operator_two,
      map_sub, map_mul, map_neg]

theorem rational_operator {C : Type*} [Ring C] [Algebra ℚ C]
    (e x : C) (he : e * e = 0) (k : ℕ) :
    CFSGSquareZeroDividedPowers.operator e k x = operator ℚ e k x := by
  by_cases hk : 3 ≤ k
  · rw [CFSGSquareZeroDividedPowers.operator_large e x he k hk,
      operator_large ℚ e x k hk]
  · have hlt : k < 3 := by omega
    interval_cases k
    · simp only [CFSGSquareZeroDividedPowers.operator_zero, operator_zero]
    · rw [CFSGSquareZeroDividedPowers.operator_one, operator_one]
      exact Ring.lie_def e x
    · rw [CFSGSquareZeroDividedPowers.operator_two e x he, operator_two]

end SymmetricSubgroupAsymptotics.CFSGIntegralSquareZeroOperators
