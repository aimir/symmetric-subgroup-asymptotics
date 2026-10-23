import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryAdmissibleIndexLower
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsParameters
import SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexBounds

/-! The uniform numerical installation of a proved unitary raw outer
bound. The actual model automorphism bound is deliberately an argument
here; this lemma does not assert or install that unproved structural fact.
The field-power index lower bound is already proved for every admissible
unitary rank, including q=2 in higher ranks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open PrimitiveSocleRawStructure

theorem twistedA_admissible_leastProperIndex_five_le
    (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower) (hsmall : r = 2 → q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedA r q) ell) : 5 ≤ ell := by
  have hl := twistedA_admissible_order_power_le_leastProperIndex r hr q hsmall ell hell
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  by_cases htwo : r = 2
  · subst r
    have hq3 : 3 ≤ q.order := by have := hsmall rfl; omega
    have hh : 3 ^ 2 ≤ q.order ^ 2 := Nat.pow_le_pow_left hq3 2
    norm_num at hh
    omega
  · have hh : 2 ^ 3 ≤ q.order ^ r :=
      (Nat.pow_le_pow_left hq 3).trans (Nat.pow_le_pow_right (by omega) (by omega))
    norm_num at hh
    omega

theorem twistedA_outer_log_three_of_raw
    (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower) (hsmall : r = 2 → q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)] (ell out : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedA r q) ell)
    (hraw : out ≤ 2 * (r + 1) * q.exponent) :
    (out : ℝ) ≤ 3 * Real.logb 2 ell := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hf : (q.exponent : ℝ) ≤ Real.logb 2 q.order :=
    CFSGFiniteFieldAutomorphisms.primePower_exponent_le_logb q
  have hrf : (r : ℝ) * q.exponent ≤ Real.logb 2 ell :=
    (mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg r)).trans
      (twistedA_admissible_rank_mul_log_order_le_log_leastProperIndex r hr q hsmall ell hell)
  have hc : (2 : ℝ) * ((r : ℝ) + 1) ≤ 3 * r := by linarith
  have hm := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg q.exponent)
  have ho : (out : ℝ) ≤ 2 * ((r : ℝ) + 1) * q.exponent := by exact_mod_cast hraw
  nlinarith

theorem twistedA_outer_budget_of_raw
    (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower) (hsmall : r = 2 → q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)] (ell out : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedA r q) ell)
    (hraw : out ≤ 2 * (r + 1) * q.exponent) : SufficientOuterOrderBudget ell out :=
  SufficientOuterOrderBudget.of_sharp
    (twistedA_admissible_leastProperIndex_five_le r hr q hsmall ell hell)
    (twistedA_outer_log_three_of_raw r hr q hsmall ell out hell hraw)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
