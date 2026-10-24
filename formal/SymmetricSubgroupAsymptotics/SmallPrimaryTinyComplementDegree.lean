import SymmetricSubgroupAsymptotics.PrimeToSmallComplementEntropy

/-! An actual factorization frontier, independent of all groups and
scalar fits. If the other primary powers are at most four, the literal
prime-to-q part divides lcm(1,...,4)=12. It is not replaced by a free
small integer unrelated to the actual degree. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.SmallPrimaryTinyComplementDegree

theorem otherPart_dvd_twelve (q t : ℕ) (ht : t ≠ 0)
    (hother : ∀ r ∈ t.primeFactors, r ≠ q → r^t.factorization r ≤ 4) :
    t/q^t.factorization q ∣ 12 := by
  have hh := TraceyElementarySharperLogBudget.otherPart_dvd_lcmUpto q t 4 ht (by decide) hother
  simpa only [show Nat.lcmUpto 4 = 12 by decide] using hh

theorem degree_data (q t : ℕ) (hq : q.Prime) (ht : t ≠ 0)
    (hother : ∀ r ∈ t.primeFactors, r ≠ q → r^t.factorization r ≤ 4) :
    ∃ k : ℕ, 1 ≤ k ∧ k ∣ 12 ∧ Nat.Coprime (q^t.factorization q) k ∧
      t = q^t.factorization q*k := by
  refine ⟨t/q^t.factorization q,?_,otherPart_dvd_twelve q t ht hother,?_,?_⟩
  · exact Nat.ordCompl_pos q ht
  · exact (Nat.coprime_ordCompl hq ht).pow_left _
  · exact (Nat.ordProj_mul_ordCompl_eq_self t q).symm

theorem degree_le (q t : ℕ) (ht : t ≠ 0) (hM : q^t.factorization q < 64)
    (hother : ∀ r ∈ t.primeFactors, r ≠ q → r^t.factorization r ≤ 4) : t ≤ 756 := by
  have hk := Nat.le_of_dvd (by decide : 0 < 12) (otherPart_dvd_twelve q t ht hother)
  have hprod := Nat.mul_le_mul (show q^t.factorization q ≤ 63 by omega) hk
  rw [Nat.ordProj_mul_ordCompl_eq_self] at hprod
  exact hprod

end SymmetricSubgroupAsymptotics.SmallPrimaryTinyComplementDegree
