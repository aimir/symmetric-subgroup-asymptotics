import SymmetricSubgroupAsymptotics.CFSGFieldFactorPermutationBudget
import SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexBounds

/-! A quadratic field-power degree lower bound suffices for the actual
8f outer estimate, refined to 4f in characteristic two. Retaining the
prime in the logarithm gives the sharp 3 log₂(ell) bound uniformly; no
extra low-degree case or cubic degree lower bound is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDOuterBudgetNumerics
open CFSGFiniteFieldAutomorphisms CFSGFieldFactorPermutationBudget PrimitiveSocleRawStructure

theorem log_three_of_square_lower (q : CFSG.PrimePower) (ell out : ℕ)
    (hdegree : q.order ^ 2 ≤ ell) (hraw : out ≤ 8 * q.exponent)
    (hbinary : q.prime = 2 → out ≤ 4 * q.exponent) :
    (out : ℝ) ≤ 3 * Real.logb 2 ell := by
  by_cases hp : q.prime = 2
  · have hcoef : (2 : ℕ) ^ 4 ≤ q.prime ^ (3 * 2) := by rw [hp]; norm_num
    have he := field_factor_le_log_of_power q 4 2 ell hdegree hcoef
    rw [primePower_card_ringAut] at he
    exact (show (out : ℝ) ≤ 4 * q.exponent by exact_mod_cast hbinary hp).trans he
  · have hp3 : 3 ≤ q.prime := by have := q.prime_isPrime.two_le; omega
    have hcoef : (2 : ℕ) ^ 8 ≤ q.prime ^ (3 * 2) :=
      (by norm_num : (2 : ℕ) ^ 8 ≤ 3 ^ 6).trans (Nat.pow_le_pow_left hp3 6)
    have he := field_factor_le_log_of_power q 8 2 ell hdegree hcoef
    rw [primePower_card_ringAut] at he
    exact (show (out : ℝ) ≤ 8 * q.exponent by exact_mod_cast hraw).trans he

theorem budget_of_square_lower (q : CFSG.PrimePower) (ell out : ℕ)
    (hdegree : q.order ^ 2 ≤ ell) (hraw : out ≤ 8 * q.exponent)
    (hbinary : q.prime = 2 → out ≤ 4 * q.exponent) : SufficientOuterOrderBudget ell out := by
  have hout := log_three_of_square_lower q ell out hdegree hraw hbinary
  have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hell : 1 ≤ ell := by
    have he := (Nat.pow_le_pow_left hq2 2).trans hdegree
    norm_num at he
    omega
  have hL : 0 ≤ Real.logb 2 (ell : ℝ) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hell)
  refine ⟨by linarith, fun _ => hout, ?_⟩
  intro hs
  have he : (ell : ℝ) ≤ (2 : ℝ) ^ 5 := by exact_mod_cast (show ell ≤ 2 ^ 5 by omega)
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (show 0 < ell by omega)) he
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
  norm_num at hl
  have ho : (out : ℝ) ≤ 24 := by linarith
  exact_mod_cast ho

end SymmetricSubgroupAsymptotics.CFSGTwistedDOuterBudgetNumerics
