import SymmetricSubgroupAsymptotics.SmallPrimaryTinyComplementDegree

/-! The actual ternary primary has complementary part dividing four,
not a free divisor of twelve. Power monotonicity then gives the two
whole primary intervals needed by the dimension-two margins. No top
actions or group representatives are enumerated. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.TinyComplementTernaryDegree

theorem otherPart_dvd_four (t : ℕ) (ht : t ≠ 0)
    (hother : ∀ r ∈ t.primeFactors, r ≠ 3 → r^t.factorization r ≤ 4) :
    t/3^t.factorization 3 ∣ 4 := by
  have hd := SmallPrimaryTinyComplementDegree.otherPart_dvd_twelve 3 t ht hother
  have hcop : Nat.Coprime (t/3^t.factorization 3) 3 := (Nat.coprime_ordCompl Nat.prime_three ht).symm
  exact hcop.dvd_mul_left.mp (by simpa only [show (3 : ℕ)*4 = 12 by decide] using hd)

theorem degree_le_four_mul_primary (t : ℕ) (ht : t ≠ 0)
    (hother : ∀ r ∈ t.primeFactors, r ≠ 3 → r^t.factorization r ≤ 4) :
    t ≤ 3^t.factorization 3*4 := by
  have hk := Nat.le_of_dvd (by decide : 0 < 4) (otherPart_dvd_four t ht hother)
  have hh := Nat.mul_le_mul_left (3^t.factorization 3) hk
  rwa [Nat.ordProj_mul_ordCompl_eq_self] at hh

theorem primary_le_twenty_seven (a : ℕ) (hsmall : 3^a < 64) : 3^a ≤ 27 := by
  have ha : a ≤ 3 := by
    by_contra hh
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 3) (show 4 ≤ a by omega)
    norm_num at hpow
    omega
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 3) ha
  simpa only [show (3 : ℕ)^3 = 27 by decide] using hpow

theorem short_primary_eq_nine (a : ℕ) (hlo : 7 ≤ 3^a) (hhi : 3^a < 16) : 3^a = 9 := by
  have ha2 : 2 ≤ a := by
    by_contra hh
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 3) (show a ≤ 1 by omega)
    norm_num at hpow
    omega
  have ha2' : a ≤ 2 := by
    by_contra hh
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 3) (show 3 ≤ a by omega)
    norm_num at hpow
    omega
  rw [show a = 2 by omega]
  decide

end SymmetricSubgroupAsymptotics.TinyComplementTernaryDegree
