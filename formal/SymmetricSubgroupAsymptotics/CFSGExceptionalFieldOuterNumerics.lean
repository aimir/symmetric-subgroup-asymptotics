import SymmetricSubgroupAsymptotics.CFSGFieldFactorPermutationBudget
import SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexBounds

/-! Numerical consumers for the actual exceptional field factors.
These lemmas keep the raw automorphism count as an explicit premise:
they do not assert that a model's outer group has that count. The proved
q^2 and half-q^3 index estimates suffice even for the small-degree clauses. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalFieldOuterNumerics
open CFSGFieldFactorPermutationBudget CFSGFiniteFieldAutomorphisms PrimitiveSocleRawStructure

theorem budget_of_log_three_one_le (ell out : ℕ) (hell : 1 ≤ ell)
    (hout : (out : ℝ) ≤ 3 * Real.logb 2 ell) : SufficientOuterOrderBudget ell out := by
  have hL : 0 ≤ Real.logb 2 (ell : ℝ) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hell)
  refine ⟨by linarith, fun _ => hout, ?_⟩
  intro hs
  have he : (ell : ℝ) ≤ (2 : ℝ)^5 := by exact_mod_cast (show ell ≤ 2^5 by omega)
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (show 0 < ell by omega)) he
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
  norm_num at hl
  have ho : (out : ℝ) ≤ 24 := by linarith
  exact_mod_cast ho

theorem six_field_budget_of_square_lower (q : CFSG.PrimePower) (ell out : ℕ)
    (hdegree : q.order^2 ≤ ell) (hraw : out ≤ 6*q.exponent) :
    SufficientOuterOrderBudget ell out := by
  have hcoef : (2 : ℕ)^6 ≤ q.prime^(3*2) := Nat.pow_le_pow_left q.prime_isPrime.two_le 6
  have hf := field_factor_le_log_of_power q 6 2 ell hdegree hcoef
  rw [primePower_card_ringAut] at hf
  have hout : (out : ℝ) ≤ 3*Real.logb 2 ell :=
    (show (out : ℝ) ≤ 6*q.exponent by exact_mod_cast hraw).trans hf
  have hq : 1 ≤ q.order := (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime).trans'
    (by have := q.prime_isPrime.two_le; omega)
  have hell : 1 ≤ ell := (Nat.one_le_pow _ _ hq).trans hdegree
  exact budget_of_log_three_one_le ell out hell hout

theorem three_field_budget_of_half_cube_lower (q : CFSG.PrimePower) (ell out : ℕ)
    (hdegree : q.order^3 ≤ 2*ell) (hraw : out ≤ 3*q.exponent) :
    SufficientOuterOrderBudget ell out := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hs : 4 ≤ q.order^2 := by
    have hh := Nat.pow_le_pow_left hq 2
    norm_num at hh
    exact hh
  have hc : 4*q.order ≤ q.order^3 := calc
    4*q.order ≤ q.order^2*q.order := Nat.mul_le_mul_right q.order hs
    _ = q.order^3 := (pow_succ q.order 2).symm
  have hbase : q.order^1 ≤ ell := by rw [pow_one]; omega
  have hf := field_factor_le_log_of_power q 3 1 ell hbase
    (Nat.pow_le_pow_left q.prime_isPrime.two_le 3)
  rw [primePower_card_ringAut] at hf
  have hout : (out : ℝ) ≤ 3*Real.logb 2 ell :=
    (show (out : ℝ) ≤ 3*q.exponent by exact_mod_cast hraw).trans hf
  exact budget_of_log_three_one_le ell out (by rw [pow_one] at hbase; omega) hout

end SymmetricSubgroupAsymptotics.CFSGExceptionalFieldOuterNumerics
