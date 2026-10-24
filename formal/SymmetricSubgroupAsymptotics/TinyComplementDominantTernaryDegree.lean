import SymmetricSubgroupAsymptotics.PrimeToSmallComplementEntropy

/-! A literal dominant primary of size three leaves only a complementary
part dividing two. This uses the actual primary-power divisibility into
the prime-to-three lcm, rather than an unrestricted divisor of twelve. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.TinyComplementDominantTernaryDegree

theorem otherPart_dvd_two (t : ℕ) (ht : t ≠ 0)
    (hother : ∀ r ∈ t.primeFactors, r ≠ 3 → r^t.factorization r ≤ 3) :
    t/3^t.factorization 3 ∣ 2 := by
  have hh := PrimeToSmallComplementEntropy.otherPart_dvd_primeTo_lcm 3 t 3
    Nat.prime_three ht (by decide) hother
  have heq : Nat.lcmUpto 3/3^(Nat.lcmUpto 3).factorization 3 = 2 := by decide +kernel
  simpa only [heq] using hh

theorem degree_eq_three_or_six (t : ℕ) (ht : t ≠ 0)
    (hprimary : 3^t.factorization 3 = 3)
    (hother : ∀ r ∈ t.primeFactors, r ≠ 3 → r^t.factorization r ≤ 3) :
    t = 3 ∨ t = 6 := by
  have hk := otherPart_dvd_two t ht hother
  have hprod := Nat.ordProj_mul_ordCompl_eq_self t 3
  change 3^t.factorization 3*(t/3^t.factorization 3) = t at hprod
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ hk with h | h
  · left
    rw [h,hprimary] at hprod
    omega
  · right
    rw [h,hprimary] at hprod
    omega

end SymmetricSubgroupAsymptotics.TinyComplementDominantTernaryDegree
