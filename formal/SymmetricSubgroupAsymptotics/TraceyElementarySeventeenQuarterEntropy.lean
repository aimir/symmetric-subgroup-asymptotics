import SymmetricSubgroupAsymptotics.ChebyshevThreeQuarterLogBound

/-! The sharper entropy bound on the ACTUAL integer factorization.
The prime-to part divides its literal lcm; the already proved17/4
Chebyshev bound is then transported without an asymptotic hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TraceyElementarySeventeenQuarterEntropy

theorem log_budget (p s v : ℕ) (hp : p.Prime) (hs : s ≠ 0) (hv : 1 ≤ v)
    (hpower : ∀ q ∈ s.primeFactors, q ≠ p → q^s.factorization q ≤ v) :
    Real.logb 2 (s : ℝ) ≤
      (s.factorization p : ℝ)*Real.logb 2 (p : ℝ)+(17/4)*(v : ℝ) := by
  have hdeg := TraceyElementarySharperLogBudget.degree_le_primary_mul_lcm p s v hs hv hpower
  have hdegR : (s : ℝ) ≤ (p : ℝ)^s.factorization p * (Nat.lcmUpto v : ℝ) := by
    exact_mod_cast hdeg
  have hsR : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hvR : (0 : ℝ) < Nat.lcmUpto v := by exact_mod_cast Nat.lcmUpto_pos v
  calc
    Real.logb 2 (s : ℝ) ≤
        Real.logb 2 ((p : ℝ)^s.factorization p * (Nat.lcmUpto v : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hsR hdegR
    _ = (s.factorization p : ℝ)*Real.logb 2 (p : ℝ)+
        Real.logb 2 (Nat.lcmUpto v : ℝ) := by
      rw [Real.logb_mul (pow_ne_zero _ hpR.ne') hvR.ne',Real.logb_pow]
    _ ≤ (s.factorization p : ℝ)*Real.logb 2 (p : ℝ)+(17/4)*(v : ℝ) :=
      add_le_add le_rfl (ChebyshevThreeQuarterLogBound.log_lcmUpto_le_seventeen_quarters_mul v)

theorem exists_log_budget (p s : ℕ) (hp : p.Prime) (hs : s ≠ 0) :
    ∃ v : ℕ, 1 ≤ v ∧
      (∀ q ∈ s.primeFactors, q ≠ p → q^s.factorization q ≤ v) ∧
      (v = 1 ∨ ∃ q ∈ s.primeFactors, q ≠ p ∧ v = q^s.factorization q) ∧
      Real.logb 2 (s : ℝ) ≤
        (s.factorization p : ℝ)*Real.logb 2 (p : ℝ)+(17/4)*(v : ℝ) := by
  obtain ⟨v,hv,hpower,hchoice⟩ := TraceyElementaryLogBudget.exists_largest_other_power p s
  exact ⟨v,hv,hpower,hchoice,log_budget p s v hp hs hv hpower⟩

end SymmetricSubgroupAsymptotics.TraceyElementarySeventeenQuarterEntropy
