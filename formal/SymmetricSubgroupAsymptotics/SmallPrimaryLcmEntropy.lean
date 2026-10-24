import SymmetricSubgroupAsymptotics.PrimeToSmallComplementEntropy
import Mathlib.Tactic.IntervalCases

/-! Exact bounded lcm entropy, independent of any group or action
catalogue. The finite reduction concerns only the sixty-four integers
0,...,63. Actual primary-power bounds imply divisibility into this same
literal lcm, rather than assuming a logarithmic fit. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallPrimaryLcmEntropy

private theorem lcm_square_first (M : ℕ) (hM : M ≤ 15) : (Nat.lcmUpto M)^2 ≤ 2^(3*M) := by
  interval_cases M <;> decide +kernel

private theorem lcm_square_second (M : ℕ) (hlo : 16 ≤ M) (hhi : M ≤ 31) :
    (Nat.lcmUpto M)^2 ≤ 2^(3*M) := by
  interval_cases M <;> decide +kernel

private theorem lcm_square_third (M : ℕ) (hlo : 32 ≤ M) (hhi : M ≤ 47) :
    (Nat.lcmUpto M)^2 ≤ 2^(3*M) := by
  interval_cases M <;> decide +kernel

private theorem lcm_square_fourth (M : ℕ) (hlo : 48 ≤ M) (hhi : M ≤ 63) :
    (Nat.lcmUpto M)^2 ≤ 2^(3*M) := by
  interval_cases M <;> decide +kernel

theorem lcm_square_le (M : ℕ) (hM : M ≤ 63) : (Nat.lcmUpto M)^2 ≤ 2^(3*M) := by
  by_cases h15 : M ≤ 15
  · exact lcm_square_first M h15
  by_cases h31 : M ≤ 31
  · exact lcm_square_second M (by omega) h31
  by_cases h47 : M ≤ 47
  · exact lcm_square_third M (by omega) h47
  · exact lcm_square_fourth M (by omega) hM

theorem log_lcm_le (M : ℕ) (hM : M ≤ 63) :
    Real.logb 2 (Nat.lcmUpto M : ℝ) ≤ (3/2)*(M : ℝ) := by
  have hpow : (Nat.lcmUpto M : ℝ)^2 ≤ (2 : ℝ)^(3*M) := by
    exact_mod_cast lcm_square_le M hM
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by exact_mod_cast Nat.lcmUpto_pos M : (0 : ℝ) < Nat.lcmUpto M) 2) hpow
  rw [Real.logb_pow,Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hh
  push_cast at hh
  linarith only [hh]

theorem degree_log_le (t M : ℕ) (ht : t ≠ 0) (hM : M ≤ 63)
    (hmax : ∀ q ∈ t.primeFactors, q^t.factorization q ≤ M) :
    Real.logb 2 (t : ℝ) ≤ (3/2)*(M : ℝ) := by
  have hdiv : t ∣ Nat.lcmUpto M := by
    apply (Nat.factorization_le_iff_dvd ht (Nat.lcmUpto_ne_zero M)).mp
    intro q
    by_cases hq : q ∈ t.primeFactors
    · have hprime := Nat.prime_of_mem_primeFactors hq
      have hM0 : M ≠ 0 := by
        have hh : 0 < q^t.factorization q := pow_pos hprime.pos _
        have hm := hmax q hq
        omega
      rw [Nat.factorization_lcmUpto M hprime]
      exact (Nat.le_log_iff_pow_le hprime.one_lt hM0).mpr (hmax q hq)
    · have hz : t.factorization q = 0 := by
        by_contra hne
        exact hq (Finsupp.mem_support_iff.mpr hne)
      rw [hz]
      exact Nat.zero_le _
  have hle := Nat.le_of_dvd (Nat.lcmUpto_pos M) hdiv
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast Nat.pos_of_ne_zero ht : (0 : ℝ) < t)
    (by exact_mod_cast hle : (t : ℝ) ≤ Nat.lcmUpto M)
  exact hh.trans (log_lcm_le M hM)

end SymmetricSubgroupAsymptotics.SmallPrimaryLcmEntropy
