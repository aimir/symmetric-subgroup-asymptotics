import Mathlib.GroupTheory.PGroup

/-! An upper bound by a power of the defining prime is a divisibility
bound for the actual cardinal of a finite p-group. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.PGroupCardPowerDivisibility

theorem card_dvd_prime_pow_of_le {G : Type*} [Group G] [Finite G]
    {p a : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    (ha : Nat.card G ≤ p ^ a) : Nat.card G ∣ p ^ a := by
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hG
  have hpow : p ^ b ≤ p ^ a := by simpa only [hb] using ha
  have hba : b ≤ a :=
    (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).two_le).mp hpow
  rw [hb]
  exact Nat.pow_dvd_pow p hba

end SymmetricSubgroupAsymptotics.PGroupCardPowerDivisibility
