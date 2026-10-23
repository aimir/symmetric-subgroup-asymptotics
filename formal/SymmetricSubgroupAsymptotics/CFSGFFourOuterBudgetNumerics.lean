import SymmetricSubgroupAsymptotics.CFSGExceptionalFieldOuterNumerics

/-! A proved 2f raw outer bound and q <= ell suffice for every required
F4 numerical clause. The structural raw bound remains explicit here;
this numerical lemma does not assume it for any original model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOuterBudgetNumerics
open CFSGExceptionalFieldOuterNumerics CFSGFieldFactorPermutationBudget
open CFSGFiniteFieldAutomorphisms PrimitiveSocleRawStructure

theorem budget_of_base_lower (q : CFSG.PrimePower) (ell out : ℕ)
    (hdegree : q.order ≤ ell) (hraw : out ≤ 2*q.exponent) : SufficientOuterOrderBudget ell out := by
  have hcoef : (2 : ℕ)^2 ≤ q.prime^(3*1) :=
    (by norm_num : (2 : ℕ)^2 ≤ 2^3).trans (Nat.pow_le_pow_left q.prime_isPrime.two_le 3)
  have hf := field_factor_le_log_of_power q 2 1 ell (by simpa only [pow_one] using hdegree) hcoef
  rw [primePower_card_ringAut] at hf
  have hout : (out : ℝ) ≤ 3*Real.logb 2 ell :=
    (show (out : ℝ) ≤ 2*q.exponent by exact_mod_cast hraw).trans hf
  have hq : 1 ≤ q.order := by
    have htwo : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    omega
  exact budget_of_log_three_one_le ell out (hq.trans hdegree) hout

end SymmetricSubgroupAsymptotics.CFSGFFourOuterBudgetNumerics
