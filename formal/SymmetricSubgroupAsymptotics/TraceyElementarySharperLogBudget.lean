import SymmetricSubgroupAsymptotics.TraceyElementaryLogBudget
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Linear entropy from the ACTUAL largest prime-to-characteristic
prime power. The original complementary part divides lcm(1,...,v),
proved by prime valuations. Existing proved Chebyshev bounds then give
log2(other part)<=8v; no eventual-degree or finite-frontier assumption
is introduced. This strengthens the old discarded quadratic entropy. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.TraceyElementarySharperLogBudget

theorem otherPart_dvd_lcmUpto (p s v : ℕ) (hs : s ≠ 0) (hv : 1 ≤ v)
    (hpower : ∀ q ∈ s.primeFactors, q ≠ p → q^s.factorization q ≤ v) :
    s / p^s.factorization p ∣ Nat.lcmUpto v := by
  apply (Nat.factorization_le_iff_dvd (Nat.ordCompl_pos p hs).ne'
    (Nat.lcmUpto_ne_zero v)).mp
  rw [Nat.factorization_ordCompl]
  intro q
  by_cases hqp : q = p
  · subst q
    simp only [Finsupp.erase_same]
    exact Nat.zero_le _
  · rw [Finsupp.erase_ne hqp]
    by_cases hq : q ∈ s.primeFactors
    · have hprime := Nat.prime_of_mem_primeFactors hq
      rw [Nat.factorization_lcmUpto v hprime]
      exact (Nat.le_log_iff_pow_le hprime.one_lt (by omega : v ≠ 0)).mpr
        (hpower q hq hqp)
    · have hz : s.factorization q = 0 := by
        by_contra hne
        exact hq (Finsupp.mem_support_iff.mpr hne)
      rw [hz]
      exact Nat.zero_le _

theorem degree_le_primary_mul_lcm (p s v : ℕ) (hs : s ≠ 0) (hv : 1 ≤ v)
    (hpower : ∀ q ∈ s.primeFactors, q ≠ p → q^s.factorization q ≤ v) :
    s ≤ p^s.factorization p * Nat.lcmUpto v := by
  have hd := otherPart_dvd_lcmUpto p s v hs hv hpower
  have hle := Nat.le_of_dvd (Nat.lcmUpto_pos v) hd
  calc
    s = p^s.factorization p * (s / p^s.factorization p) :=
      (Nat.ordProj_mul_ordCompl_eq_self s p).symm
    _ ≤ p^s.factorization p * Nat.lcmUpto v := Nat.mul_le_mul_left _ hle

theorem log_lcmUpto_le_eight_mul (v : ℕ) :
    Real.logb 2 (Nat.lcmUpto v : ℝ) ≤ 8*(v : ℝ) := by
  rw [Real.logb,div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  rw [←Chebyshev.psi_eq_log_lcmUpto]
  have hh := Chebyshev.psi_le_const_mul_self (show (0 : ℝ) ≤ v by positivity)
  have hlog : (2 : ℝ)/3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hfour : Real.log 4 = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num
  rw [hfour] at hh
  have hv : (0 : ℝ) ≤ v := by positivity
  nlinarith

theorem log_budget_linear (p s v : ℕ) (hp : p.Prime) (hs : s ≠ 0) (hv : 1 ≤ v)
    (hpower : ∀ q ∈ s.primeFactors, q ≠ p → q^s.factorization q ≤ v) :
    Real.logb 2 (s : ℝ) ≤ (s.factorization p : ℝ)*Real.logb 2 (p : ℝ) + 8*(v : ℝ) := by
  have hdeg := degree_le_primary_mul_lcm p s v hs hv hpower
  have hdegR : (s : ℝ) ≤ (p : ℝ)^s.factorization p * (Nat.lcmUpto v : ℝ) := by
    exact_mod_cast hdeg
  have hsR : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hvR : (0 : ℝ) < Nat.lcmUpto v := by exact_mod_cast Nat.lcmUpto_pos v
  calc
    Real.logb 2 (s : ℝ) ≤
        Real.logb 2 ((p : ℝ)^s.factorization p * (Nat.lcmUpto v : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hsR hdegR
    _ = (s.factorization p : ℝ)*Real.logb 2 (p : ℝ) +
        Real.logb 2 (Nat.lcmUpto v : ℝ) := by
      rw [Real.logb_mul (pow_ne_zero _ hpR.ne') hvR.ne',Real.logb_pow]
    _ ≤ (s.factorization p : ℝ)*Real.logb 2 (p : ℝ) + 8*(v : ℝ) :=
      add_le_add le_rfl (log_lcmUpto_le_eight_mul v)

theorem exists_linear_log_budget (p s : ℕ) (hp : p.Prime) (hs : s ≠ 0) :
    ∃ v : ℕ, 1 ≤ v ∧
      (∀ q ∈ s.primeFactors, q ≠ p → q^s.factorization q ≤ v) ∧
      (v = 1 ∨ ∃ q ∈ s.primeFactors, q ≠ p ∧ v = q^s.factorization q) ∧
      Real.logb 2 (s : ℝ) ≤
        (s.factorization p : ℝ)*Real.logb 2 (p : ℝ) + 8*(v : ℝ) := by
  obtain ⟨v,hv,hpower,hchoice⟩ := TraceyElementaryLogBudget.exists_largest_other_power p s
  exact ⟨v,hv,hpower,hchoice,log_budget_linear p s v hp hs hv hpower⟩

end SymmetricSubgroupAsymptotics.TraceyElementarySharperLogBudget
