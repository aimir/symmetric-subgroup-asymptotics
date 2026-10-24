import SymmetricSubgroupAsymptotics.TraceyElementarySharperLogBudget

/-! Literal complementary-divisor control. Removing the primary prime
from the actual lcm preserves divisibility, and complementary powers
below sixteen give one uniform entropy constant. The finite reduction is
only the integer lcm(1,...,15), never a group or action catalogue. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimeToSmallComplementEntropy

theorem otherPart_dvd_primeTo_lcm (p s v : ℕ) (hp : p.Prime) (hs : s ≠ 0)
    (hv : 1 ≤ v)
    (hpower : ∀ q ∈ s.primeFactors, q ≠ p → q^s.factorization q ≤ v) :
    s / p^s.factorization p ∣ Nat.lcmUpto v / p^(Nat.lcmUpto v).factorization p := by
  exact Nat.dvd_ordCompl_of_dvd_not_dvd
    (TraceyElementarySharperLogBudget.otherPart_dvd_lcmUpto p s v hs hv hpower)
    (Nat.not_dvd_ordCompl hp hs)

theorem log_lcm_fifteen_le : Real.logb 2 (Nat.lcmUpto 15 : ℝ) ≤ 19 := by
  have hnat : Nat.lcmUpto 15 ≤ 2^19 := by decide +kernel
  have hreal : (Nat.lcmUpto 15 : ℝ) ≤ (2 : ℝ)^19 := by exact_mod_cast hnat
  have hpos : (0 : ℝ) < Nat.lcmUpto 15 := by exact_mod_cast Nat.lcmUpto_pos 15
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos hreal
  rw [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hh
  norm_num only [Nat.cast_ofNat] at hh
  exact hh

theorem log_budget_of_other_powers_lt_sixteen (p s : ℕ) (hp : p.Prime) (hs : s ≠ 0)
    (hpower : ∀ q ∈ s.primeFactors, q ≠ p → q^s.factorization q < 16) :
    Real.logb 2 (s : ℝ) ≤ (s.factorization p : ℝ)*Real.logb 2 (p : ℝ)+19 := by
  have hdeg := TraceyElementarySharperLogBudget.degree_le_primary_mul_lcm p s 15 hs
    (by decide) (fun q hq hqp => by have hh := hpower q hq hqp; omega)
  have hreal : (s : ℝ) ≤ (p : ℝ)^s.factorization p*(Nat.lcmUpto 15 : ℝ) := by
    exact_mod_cast hdeg
  have hspos : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlcmpos : (0 : ℝ) < Nat.lcmUpto 15 := by exact_mod_cast Nat.lcmUpto_pos 15
  calc
    Real.logb 2 (s : ℝ) ≤
        Real.logb 2 ((p : ℝ)^s.factorization p*(Nat.lcmUpto 15 : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hspos hreal
    _ = (s.factorization p : ℝ)*Real.logb 2 (p : ℝ)+
        Real.logb 2 (Nat.lcmUpto 15 : ℝ) := by
      rw [Real.logb_mul (pow_ne_zero _ hppos.ne') hlcmpos.ne',Real.logb_pow]
    _ ≤ (s.factorization p : ℝ)*Real.logb 2 (p : ℝ)+19 :=
      add_le_add le_rfl log_lcm_fifteen_le

theorem primary_product_ge_six (q a : ℕ) (hq : 3 ≤ q) (ha : 1 ≤ a)
    (hM : 64 ≤ q^a) : 6 ≤ (q-1)*a := by
  by_contra hh
  have hprod : (q-1)*a ≤ 5 := by omega
  have hsub : q-1+1 = q := by omega
  have htwo : 2 ≤ q-1 := by omega
  have hmul := Nat.mul_le_mul_right a htwo
  have ha2 : a ≤ 2 := by nlinarith only [hmul,hprod]
  have hcases : a = 1 ∨ a = 2 := by omega
  rcases hcases with rfl | rfl
  · simp only [mul_one,pow_one] at hprod hM
    omega
  · have hq3 : q ≤ 3 := by omega
    have hpow : q^2 ≤ 9 := by nlinarith only [hq,hq3]
    omega

end SymmetricSubgroupAsymptotics.PrimeToSmallComplementEntropy
