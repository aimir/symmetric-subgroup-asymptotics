import SymmetricSubgroupAsymptotics.CFSGIntegralQuadraticRootOperators
import Mathlib.Tactic.IntervalCases

/-! Exact anti-multiplicative transport of the quadratic root coefficients.
The sign (-1)^k is essential; plain transpose is not a Lie homomorphism. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.QuadraticRootOperatorAntiTransport
variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
  (T : B →ₗ[R] B) (hT : ∀ x y, T (x * y) = T y * T x)

include hT

theorem operator (e d x : B) (k : ℕ) :
    T (CFSGIntegralQuadraticRootOperators.operator R e d k x) =
      ((-1 : R) ^ k) • CFSGIntegralQuadraticRootOperators.operator R (T e) (T d) k (T x) := by
  by_cases hk : 5 ≤ k
  · rw [CFSGIntegralQuadraticRootOperators.operator_large R e d x k hk,
      CFSGIntegralQuadraticRootOperators.operator_large R (T e) (T d) (T x) k hk,
      map_zero, smul_zero]
  · have hlt : k < 5 := by omega
    interval_cases k <;>
      simp only [CFSGIntegralQuadraticRootOperators.operator_zero,
        CFSGIntegralQuadraticRootOperators.operator_one,
        CFSGIntegralQuadraticRootOperators.operator_two,
        CFSGIntegralQuadraticRootOperators.operator_three,
        CFSGIntegralQuadraticRootOperators.operator_four,
        map_add, map_sub, hT, pow_succ, pow_zero, neg_mul, mul_neg, neg_neg,
        one_mul, mul_one, one_smul, neg_one_smul, mul_assoc] <;> abel

end SymmetricSubgroupAsymptotics.QuadraticRootOperatorAntiTransport
