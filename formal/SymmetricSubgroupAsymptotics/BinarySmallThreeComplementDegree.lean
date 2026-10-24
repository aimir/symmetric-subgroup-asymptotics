import SymmetricSubgroupAsymptotics.PrimeToSmallComplementEntropy

/-! Actual complementary powers at most three leave only a pure binary
degree or three times its exact binary primary part. The small interval
uses integer powers and logarithm monotonicity, with no real evaluation or
enumeration of exponents. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinarySmallThreeComplementDegree

theorem eq_binary_or_three_mul (t : ℕ) (ht : t ≠ 0)
    (hother : ∀ q ∈ t.primeFactors, q ≠ 2 → q ^ t.factorization q ≤ 3) :
    t = 2 ^ t.factorization 2 ∨ t = 3 * 2 ^ t.factorization 2 := by
  have hc := PrimeToSmallComplementEntropy.otherPart_dvd_primeTo_lcm
    2 t 3 Nat.prime_two ht (by decide) hother
  have hlcm : Nat.lcmUpto 3 / 2 ^ (Nat.lcmUpto 3).factorization 2 = 3 := by decide +kernel
  rw [hlcm] at hc
  have hprod : 2 ^ t.factorization 2 * (t / 2 ^ t.factorization 2) = t :=
    Nat.ordProj_mul_ordCompl_eq_self t 2
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hc with h | h
  · left
    rw [h,mul_one] at hprod
    exact hprod.symm
  · right
    rw [h] at hprod
    exact hprod.symm.trans (mul_comm _ _)

theorem interval_of_three_mul_binary (t a : ℕ) (ha6 : 6 ≤ a) (ha7 : a ≤ 7)
    (ht : t = 3 * 2 ^ a) :
    192 ≤ t ∧ 7 ≤ Real.logb 2 (t : ℝ) ∧ Real.logb 2 (t : ℝ) ≤ 43 / 5 := by
  have hpow : (2 : ℕ) ^ 6 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) ha6
  have ht192 : 192 ≤ t := by
    calc
      192 = 3 * (2 : ℕ) ^ 6 := by decide
      _ ≤ 3 * 2 ^ a := Nat.mul_le_mul_left 3 hpow
      _ = t := ht.symm
  have hthree_lower : (1 : ℝ) ≤ Real.logb 2 3 := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3)
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hh
  have hthree_upper : Real.logb 2 (3 : ℝ) ≤ 8 / 5 := by
    have hp : (3 : ℝ) ^ (5 : ℕ) ≤ (2 : ℝ) ^ (8 : ℕ) := by norm_num
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (3 : ℝ) ^ (5 : ℕ)) hp
    rw [Real.logb_pow,Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have htR : (t : ℝ) = 3 * (2 : ℝ) ^ a := by exact_mod_cast ht
  have hlog : Real.logb 2 (t : ℝ) = Real.logb 2 (3 : ℝ) + (a : ℝ) := by
    rw [htR,Real.logb_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity : (2 : ℝ) ^ a ≠ 0),
      Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
  have ha6R : (6 : ℝ) ≤ a := by exact_mod_cast ha6
  have ha7R : (a : ℝ) ≤ 7 := by exact_mod_cast ha7
  refine ⟨ht192,?_,?_⟩
  · rw [hlog]
    linarith
  · rw [hlog]
    linarith

end SymmetricSubgroupAsymptotics.BinarySmallThreeComplementDegree
