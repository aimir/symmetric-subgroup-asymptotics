import SymmetricSubgroupAsymptotics.LargestPrimePowerQuadraticEntropy

/-! When the actual largest primary is binary or ternary and less than8,
its genuine original degree is one of five tiny integers. Divisibility
by lcm(1,...,M), not an action catalogue, proves the exhaustion. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.SmallMatchingDominantPrimaryDegrees

theorem degree_eq (t q : ℕ) (ht : 2 ≤ t) (hq : q ∈ t.primeFactors)
    (hmax : ∀ p ∈ t.primeFactors, p^t.factorization p ≤ q^t.factorization q)
    (hM : q^t.factorization q < 8) (hq23 : q = 2 ∨ q = 3) :
    t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 6 ∨ t = 12 := by
  have ht0 : t ≠ 0 := by omega
  have he : 1 ≤ t.factorization q := by
    have hn : t.factorization q ≠ 0 := Finsupp.mem_support_iff.mp hq
    omega
  rcases hq23 with rfl | rfl
  · have he2 : t.factorization 2 ≤ 2 := by
      by_contra hn
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2)
        (show 3 ≤ t.factorization 2 by omega)
      norm_num at hp
      omega
    have heq : t.factorization 2 = 1 ∨ t.factorization 2 = 2 := by omega
    rcases heq with heq | heq
    · have hmax2 : ∀ p ∈ t.primeFactors, p^t.factorization p ≤ 2 := by
        simpa only [heq,pow_one] using hmax
      have hd := LargestPrimePowerQuadraticEntropy.degree_dvd_lcmUpto t 2 ht0 (by decide) hmax2
      have hd2 : t ∣ 2 := by simpa only [show Nat.lcmUpto 2 = 2 by decide] using hd
      have hle := Nat.le_of_dvd (by decide : 0 < 2) hd2
      exact Or.inl (by omega)
    · have hmax4 : ∀ p ∈ t.primeFactors, p^t.factorization p ≤ 4 := by
        simpa only [heq,show (2 : ℕ)^2 = 4 by decide] using hmax
      have hd := LargestPrimePowerQuadraticEntropy.degree_dvd_lcmUpto t 4 ht0 (by decide) hmax4
      have hd12 : t ∣ 12 := by simpa only [show Nat.lcmUpto 4 = 12 by decide] using hd
      have hle := Nat.le_of_dvd (by decide : 0 < 12) hd12
      have h4 : 4 ∣ t := by
        simpa only [heq,show (2 : ℕ)^2 = 4 by decide] using Nat.ordProj_dvd t 2
      have hmod := Nat.mod_eq_zero_of_dvd h4
      have hge := Nat.le_of_dvd (show 0 < t by omega) h4
      have heq' : t = 4 ∨ t = 8 ∨ t = 12 := by omega
      rcases heq' with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · norm_num at hd12
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · have he1 : t.factorization 3 = 1 := by
      by_contra hn
      have hp := Nat.pow_le_pow_right (by decide : 0 < 3)
        (show 2 ≤ t.factorization 3 by omega)
      norm_num at hp
      omega
    have hmax3 : ∀ p ∈ t.primeFactors, p^t.factorization p ≤ 3 := by
      simpa only [he1,pow_one] using hmax
    have hd := LargestPrimePowerQuadraticEntropy.degree_dvd_lcmUpto t 3 ht0 (by decide) hmax3
    have hd6 : t ∣ 6 := by simpa only [show Nat.lcmUpto 3 = 6 by decide] using hd
    have hle := Nat.le_of_dvd (by decide : 0 < 6) hd6
    have h3 : 3 ∣ t := by simpa only [he1,pow_one] using Nat.ordProj_dvd t 3
    have hmod := Nat.mod_eq_zero_of_dvd h3
    have hge := Nat.le_of_dvd (show 0 < t by omega) h3
    have heq : t = 3 ∨ t = 6 := by omega
    rcases heq with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

end SymmetricSubgroupAsymptotics.SmallMatchingDominantPrimaryDegrees
