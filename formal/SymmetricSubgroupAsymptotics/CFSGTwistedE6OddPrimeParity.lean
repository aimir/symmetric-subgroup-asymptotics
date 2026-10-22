import SymmetricSubgroupAsymptotics.CFSGTwistedE6OddCharacteristicParity

/-! Exact literal-prime guard for the proved original twisted E6 parity
branch. Prime two remains an explicit mathematical obligation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2

theorem twistedE6_even_card_of_prime_ne_two (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (hq : q.prime≠2) :
    Even (Nat.card (CFSG.Models.TwistedE6 q)) := by
  apply twistedE6_even_card_of_two_ne_zero q
  intro he
  have hd : q.prime ∣ 2 := (CharP.cast_eq_zero_iff (q.Extension 2) q.prime 2).mp he
  exact hq ((Nat.prime_dvd_prime_iff_eq q.prime_isPrime Nat.prime_two).mp hd)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2
