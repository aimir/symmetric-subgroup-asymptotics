import SymmetricSubgroupAsymptotics.TraceyElementarySharperLogBudget

/-! Literal dominant prime powers for every integer degree at least two.
Both the dominant prime and the largest complementary power come from
the ACTUAL factorization. Their entropy inequalities require no action
classification, finite frontier or generator bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.LargestPrimePowerEntropy

theorem exists_largest_prime_power (t : ℕ) (ht : 2 ≤ t) :
    ∃ q ∈ t.primeFactors,
      ∀ r ∈ t.primeFactors, r^t.factorization r ≤ q^t.factorization q := by
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd (by omega : t ≠ 1)
  have hnonempty : t.primeFactors.Nonempty :=
    ⟨p,hp.mem_primeFactors hpd (by omega : t ≠ 0)⟩
  exact Finset.exists_max_image t.primeFactors (fun q => q^t.factorization q) hnonempty

theorem largest_other_le (t q v : ℕ) (hq : q.Prime)
    (hmax : ∀ r ∈ t.primeFactors, r^t.factorization r ≤ q^t.factorization q)
    (hchoice : v = 1 ∨ ∃ r ∈ t.primeFactors, r ≠ q ∧ v = r^t.factorization r) :
    v ≤ q^t.factorization q := by
  rcases hchoice with rfl | ⟨r,hr,_,rfl⟩
  · exact Nat.one_le_pow _ _ hq.pos
  · exact hmax r hr

theorem exists_largest_with_entropy (t : ℕ) (ht : 2 ≤ t) :
    ∃ q ∈ t.primeFactors, ∃ v : ℕ,
      (∀ r ∈ t.primeFactors, r^t.factorization r ≤ q^t.factorization q) ∧
      1 ≤ v ∧ v ≤ q^t.factorization q ∧
      (∀ r ∈ t.primeFactors, r ≠ q → r^t.factorization r ≤ v) ∧
      (v = 1 ∨ ∃ r ∈ t.primeFactors, r ≠ q ∧ v = r^t.factorization r) ∧
      (t.factorization q : ℝ)*Real.logb 2 (q : ℝ) ≤ Real.logb 2 (t : ℝ) ∧
      Real.logb 2 (t : ℝ) ≤
        (t.factorization q : ℝ)*Real.logb 2 (q : ℝ)+8*(v : ℝ) := by
  obtain ⟨q,hq,hmax⟩ := exists_largest_prime_power t ht
  have hprime := Nat.prime_of_mem_primeFactors hq
  obtain ⟨v,hv,hpowers,hchoice⟩ :=
    TraceyElementaryLogBudget.exists_largest_other_power q t
  have hvM := largest_other_le t q v hprime hmax hchoice
  have hproj : q^t.factorization q ≤ t :=
    Nat.le_of_dvd (by omega : 0 < t) (Nat.ordProj_dvd t q)
  have hprojR : (q : ℝ)^t.factorization q ≤ t := by exact_mod_cast hproj
  have hlower := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by exact_mod_cast hprime.pos) _) hprojR
  rw [Real.logb_pow] at hlower
  exact ⟨q,hq,v,hmax,hv,hvM,hpowers,hchoice,hlower,
    TraceyElementarySharperLogBudget.log_budget_linear q t v hprime
      (by omega : t ≠ 0) hv hpowers⟩

end SymmetricSubgroupAsymptotics.LargestPrimePowerEntropy
