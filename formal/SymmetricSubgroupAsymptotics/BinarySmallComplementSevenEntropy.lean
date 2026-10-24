import SymmetricSubgroupAsymptotics.PrimeToSmallComplementEntropy
import Mathlib.Tactic.IntervalCases

/-! One arithmetic interval for every complementary power from seven
through fifteen. The finite calculation concerns only lcm(1,...,v), not
actions, groups, dominant exponents, or scalar-fit certificates. Removing
the actual binary primary part gives the same bounds on the literal top
degree's complementary logarithm. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinarySmallComplementSevenEntropy

theorem primeTo_lcm_power_bounds (v : ℕ) (hv7 : 7 ≤ v) (hv15 : v ≤ 15) :
    Nat.lcmUpto v / 2 ^ (Nat.lcmUpto v).factorization 2 ≤ 2^16 ∧
      (Nat.lcmUpto v / 2 ^ (Nat.lcmUpto v).factorization 2)^7 ≤ 2^(v^2) := by
  interval_cases v <;> decide +kernel

theorem log_primeTo_lcm_bounds (v : ℕ) (hv7 : 7 ≤ v) (hv15 : v ≤ 15) :
    Real.logb 2 (Nat.lcmUpto v / 2 ^ (Nat.lcmUpto v).factorization 2 : ℕ) ≤ 16 ∧
      7 * Real.logb 2 (Nat.lcmUpto v / 2 ^ (Nat.lcmUpto v).factorization 2 : ℕ) ≤
        (v : ℝ)^2 := by
  let N := Nat.lcmUpto v / 2 ^ (Nat.lcmUpto v).factorization 2
  have hN : 0 < N := Nat.ordCompl_pos 2 (Nat.lcmUpto_ne_zero v)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hh := primeTo_lcm_power_bounds v hv7 hv15
  have hsmall : (N : ℝ) ≤ (2 : ℝ)^16 := by exact_mod_cast hh.1
  have hpower : (N : ℝ)^7 ≤ (2 : ℝ)^(v^2) := by exact_mod_cast hh.2
  have hlogsmall := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hNR hsmall
  have hlogpower := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos hNR 7) hpower
  rw [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hlogsmall
  rw [Real.logb_pow,Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hlogpower
  norm_num only [Nat.cast_ofNat,Nat.cast_pow] at hlogsmall hlogpower
  exact ⟨hlogsmall,hlogpower⟩

theorem otherPart_log_bounds (t v : ℕ) (ht : t ≠ 0) (hv7 : 7 ≤ v) (hv15 : v ≤ 15)
    (hother : ∀ q ∈ t.primeFactors, q ≠ 2 → q ^ t.factorization q ≤ v) :
    0 ≤ Real.logb 2 (t / 2 ^ t.factorization 2 : ℕ) ∧
      Real.logb 2 (t / 2 ^ t.factorization 2 : ℕ) ≤ 16 ∧
      7 * Real.logb 2 (t / 2 ^ t.factorization 2 : ℕ) ≤ (v : ℝ)^2 := by
  have hdiv := PrimeToSmallComplementEntropy.otherPart_dvd_primeTo_lcm
    2 t v Nat.prime_two ht (by omega) hother
  have hN := Nat.ordCompl_pos 2 (Nat.lcmUpto_ne_zero v)
  have hle := Nat.le_of_dvd hN hdiv
  have hp := Nat.ordCompl_pos 2 ht
  have hleR : ((t / 2 ^ t.factorization 2 : ℕ) : ℝ) ≤
      (Nat.lcmUpto v / 2 ^ (Nat.lcmUpto v).factorization 2 : ℕ) := by exact_mod_cast hle
  have hpR : (0 : ℝ) < (t / 2 ^ t.factorization 2 : ℕ) := by exact_mod_cast hp
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpR hleR
  have hb := log_primeTo_lcm_bounds v hv7 hv15
  refine ⟨Real.logb_nonneg (by norm_num) (by exact_mod_cast hp),hlog.trans hb.1,?_⟩
  linarith only [hlog,hb.2]

end SymmetricSubgroupAsymptotics.BinarySmallComplementSevenEntropy
