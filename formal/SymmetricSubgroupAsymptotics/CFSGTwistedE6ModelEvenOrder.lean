import SymmetricSubgroupAsymptotics.CFSGTwistedE6CharacteristicTwoParity
import SymmetricSubgroupAsymptotics.CFSGTwistedE6OddPrimeParity

/-! Every characteristic of the literal original simple twisted E6 model.
No finite-field or named-group identification is added. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2

theorem twistedE6_even_card (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] : Even (Nat.card (CFSG.Models.TwistedE6 q)) := by
  by_cases hq : q.prime=2
  · letI : CharP (q.Extension 2) 2 := by
      simpa only [hq] using (inferInstance : CharP (q.Extension 2) q.prime)
    exact twistedE6_even_card_of_characteristic_two q
  · exact twistedE6_even_card_of_prime_ne_two q hq

end SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2
