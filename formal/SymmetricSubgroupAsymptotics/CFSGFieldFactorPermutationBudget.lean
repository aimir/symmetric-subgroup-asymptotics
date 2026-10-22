import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsParameters
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexStarLower

/-! A reusable exact-characteristic field-factor budget. The original
prime-field logarithm is retained, rather than replacing it prematurely
by log2(q). Applied to the ACTUAL original D4 star lower bound, this
covers the coarse24 factor in characteristic>=7 and the sharp6 factor
in every characteristic. No stronger degree lower bound is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFieldFactorPermutationBudget
open CFSGFiniteFieldAutomorphisms

theorem field_factor_le_log_of_power (q : CFSG.PrimePower) (C d ell : ℕ)
    (hdegree : q.order ^ d ≤ ell) (hcoef : (2 : ℕ) ^ C ≤ q.prime ^ (3 * d)) :
    (C : ℝ) * (Nat.card (q.Field ≃+* q.Field) : ℝ) ≤ 3 * Real.logb 2 ell := by
  have hcR : (2 : ℝ) ^ C ≤ (q.prime : ℝ) ^ (3 * d) := by exact_mod_cast hcoef
  have hc := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ C) hcR
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hc
  have hc' : (C : ℝ) ≤ (3 * (d : ℝ)) * Real.logb 2 q.prime := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hc
  have hq : 0 < q.order := pow_pos q.prime_isPrime.pos _
  have hdR : (q.order : ℝ) ^ d ≤ (ell : ℝ) := by exact_mod_cast hdegree
  have hd := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (q.order : ℝ) ^ d) hdR
  rw [Real.logb_pow] at hd
  have hf := card_ringAut_mul_logb_characteristic q.Field q.prime
  rw [q.card_field] at hf
  calc
    (C : ℝ) * (Nat.card (q.Field ≃+* q.Field) : ℝ) ≤
        ((3 * (d : ℝ)) * Real.logb 2 q.prime) *
          (Nat.card (q.Field ≃+* q.Field) : ℝ) :=
      mul_le_mul_of_nonneg_right hc' (Nat.cast_nonneg _)
    _ = 3 * ((d : ℝ) * Real.logb 2 q.order) := by rw [← hf]; ring
    _ ≤ 3 * Real.logb 2 ell := mul_le_mul_of_nonneg_left hd (by norm_num)

theorem twenty_four_budget_of_prime_ge_seven (q : CFSG.PrimePower) (hp : 7 ≤ q.prime)
    (ell : ℕ) (hdegree : q.order ^ 3 ≤ ell) :
    (24 : ℝ) * (Nat.card (q.Field ≃+* q.Field) : ℝ) ≤ 3 * Real.logb 2 ell := by
  apply field_factor_le_log_of_power q 24 3 ell hdegree
  exact (by norm_num : (2 : ℕ) ^ 24 ≤ 7 ^ 9).trans (Nat.pow_le_pow_left hp 9)

theorem six_budget_of_cubic_degree (q : CFSG.PrimePower)
    (ell : ℕ) (hdegree : q.order ^ 3 ≤ ell) :
    (6 : ℝ) * (Nat.card (q.Field ≃+* q.Field) : ℝ) ≤ 3 * Real.logb 2 ell := by
  apply field_factor_le_log_of_power q 6 3 ell hdegree
  exact (by norm_num : (2 : ℕ) ^ 6 ≤ 2 ^ 9).trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le 9)

end SymmetricSubgroupAsymptotics.CFSGFieldFactorPermutationBudget

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGOrthogonalDSerreMatrices PrimitiveSocleRawStructure

theorem typeD_four_twenty_four_field_budget (q : CFSG.PrimePower) (hp : 7 ≤ q.prime)
    [IsSimpleGroup (CFSG.Models.D 4 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.D 4 q) ell) :
    (24 : ℝ) * (Nat.card (q.Field ≃+* q.Field) : ℝ) ≤ 3 * Real.logb 2 ell := by
  apply CFSGFieldFactorPermutationBudget.twenty_four_budget_of_prime_ge_seven q hp ell
  simpa using typeD_order_power_le_leastProperIndex 4 (by decide) q ell hell

theorem typeD_four_six_field_budget (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D 4 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.D 4 q) ell) :
    (6 : ℝ) * (Nat.card (q.Field ≃+* q.Field) : ℝ) ≤ 3 * Real.logb 2 ell := by
  apply CFSGFieldFactorPermutationBudget.six_budget_of_cubic_degree q ell
  simpa using typeD_order_power_le_leastProperIndex 4 (by decide) q ell hell

end SymmetricSubgroupAsymptotics.CFSGReduction
