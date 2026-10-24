import SymmetricSubgroupAsymptotics.BinarySmallThreeComplementDegree

/-! Generic primary-power arithmetic for the actual tiny-complement
exhaustion. Oddness eliminates the false even endpoints; the binary
exponent bound uses power monotonicity. No top actions are enumerated. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.TinyComplementPrimaryExhaustion

theorem odd_primary_cases (q a : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (ha : 1 ≤ a) :
    q^a = 3 ∨ q^a = 5 ∨ 7 ≤ q^a := by
  have hq3 : 3 ≤ q := by have hh := hq.two_le; omega
  have hqM : q ≤ q^a := by
    simpa only [pow_one] using Nat.pow_le_pow_right hq.pos ha
  have hodd : Odd (q^a) := (hq.odd_of_ne_two hq2).pow
  rcases hodd with ⟨k,hk⟩
  omega

theorem odd_primary_le_nine (q a : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hsmall : q^a < 11) : q^a ≤ 9 := by
  have hodd : Odd (q^a) := (hq.odd_of_ne_two hq2).pow
  rcases hodd with ⟨k,hk⟩
  omega

theorem other_odd_powers_le_three (t : ℕ)
    (hother : ∀ r ∈ t.primeFactors, r ≠ 2 → r^t.factorization r ≤ 4) :
    ∀ r ∈ t.primeFactors, r ≠ 2 → r^t.factorization r ≤ 3 := by
  intro r hr hr2
  have hpower := hother r hr hr2
  have hprime := Nat.prime_of_mem_primeFactors hr
  have hodd : Odd (r^t.factorization r) := (hprime.odd_of_ne_two hr2).pow
  rcases hodd with ⟨k,hk⟩
  omega

theorem binary_small_exponent (a : ℕ) (hsmall : 2^a < 64) : a ≤ 5 := by
  by_contra hh
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 6 ≤ a by omega)
  norm_num at hpow
  omega

end SymmetricSubgroupAsymptotics.TinyComplementPrimaryExhaustion
