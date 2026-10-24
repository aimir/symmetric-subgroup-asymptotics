import SymmetricSubgroupAsymptotics.PrimeToSmallComplementEntropy

/-! Actual prime-to-binary entropy when all other primary powers are
at most five. The lower logarithmic bound uses the actual factor five;
no real evaluation or list of dominant exponents is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinarySmallFiveComplementDegree

theorem otherPart_log_bounds (t : ℕ) (ht : t ≠ 0)
    (hother : ∀ q ∈ t.primeFactors, q ≠ 2 → q^t.factorization q ≤ 5) :
    0 ≤ Real.logb 2 (t / 2^t.factorization 2 : ℕ) ∧
      Real.logb 2 (t / 2^t.factorization 2 : ℕ) ≤ 4 := by
  have hdiv := PrimeToSmallComplementEntropy.otherPart_dvd_primeTo_lcm
    2 t 5 Nat.prime_two ht (by decide) hother
  have heq : Nat.lcmUpto 5 / 2^(Nat.lcmUpto 5).factorization 2 = 15 := by decide +kernel
  rw [heq] at hdiv
  have hbound := Nat.le_of_dvd (by decide : 0 < 15) hdiv
  have hpos := Nat.ordCompl_pos 2 ht
  have hposR : (0 : ℝ) < (t / 2^t.factorization 2 : ℕ) := by exact_mod_cast hpos
  have hboundR : ((t / 2^t.factorization 2 : ℕ) : ℝ) ≤ (2 : ℝ)^4 := by
    have hh : t / 2^t.factorization 2 ≤ (2 : ℕ)^4 := by omega
    exact_mod_cast hh
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hposR hboundR
  rw [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hh
  norm_num only [Nat.cast_ofNat] at hh
  exact ⟨Real.logb_nonneg (by norm_num) (by exact_mod_cast hpos),hh⟩

theorem logb_five_lower : (9/4 : ℝ) ≤ Real.logb 2 (5 : ℝ) := by
  have hp : (2 : ℝ)^9 ≤ (5 : ℝ)^4 := by norm_num
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (2 : ℝ)^9) hp
  rw [Real.logb_pow,Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith only [hh]

theorem degree_log_lower (t a : ℕ) (hprod : 2^a*5 ≤ t) :
    (a : ℝ)+9/4 ≤ Real.logb 2 (t : ℝ) := by
  have hprodR : (2 : ℝ)^a*5 ≤ t := by exact_mod_cast hprod
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (2 : ℝ)^a*5) hprodR
  rw [Real.logb_mul (by positivity : (2 : ℝ)^a ≠ 0) (by norm_num : (5 : ℝ) ≠ 0),
    Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hh
  linarith only [hh,logb_five_lower]

end SymmetricSubgroupAsymptotics.BinarySmallFiveComplementDegree
