import SymmetricSubgroupAsymptotics.CFSGPSLTwoImprovedScaledClassPacket
import SymmetricSubgroupAsymptotics.CFSGPrimePowerSmallOrders

/-! Exact field-parameter complement of the shared PSL2 packets.
This finite arithmetic certificate concerns prime powers, not actions
or subgroup catalogues. It introduces no group-theoretic premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoSmallFieldParameters
open CFSGPSLTwoImprovedScaledClassPacket

def tinyOrders : Finset ℕ := {4,5,7,8,9,25}

theorem tinyOrders_card : tinyOrders.card=6 := by decide +kernel

private theorem bounded_prime_powers : ∀ n : Fin 51, 4≤n.val → IsPrimePow n.val →
    n.val∈tinyOrders ∨ (n.val.Prime ∧ 11≤n.val) ∨
      n.val=16 ∨ n.val=32 ∨ n.val=27 ∨ n.val=49 := by
  decide +kernel

theorem improved_or_tiny (q : CFSG.PrimePower) (hq : 4≤q.order) (hupper : q.order<51) :
    FieldProfile q ∨ q.order∈tinyOrders := by
  have h := bounded_prime_powers ⟨q.order,hupper⟩ hq
    (CFSGPrimePowerSmallOrders.order_isPrimePow q)
  rcases h with ht | hp | h16 | h32 | h27 | h49
  · exact Or.inr ht
  · exact Or.inl (Or.inl hp)
  · have hp : q.prime=2 :=
      (Nat.Prime.pow_inj' q.prime_isPrime Nat.prime_two q.exponent_pos.ne'
        (by decide : (4:ℕ)≠0) (show q.prime^q.exponent=2^4 from h16)).1
    exact Or.inl (Or.inr (Or.inl ⟨hp,h16.ge⟩))
  · have hp : q.prime=2 :=
      (Nat.Prime.pow_inj' q.prime_isPrime Nat.prime_two q.exponent_pos.ne'
        (by decide : (5:ℕ)≠0) (show q.prime^q.exponent=2^5 from h32)).1
    exact Or.inl (Or.inr (Or.inl ⟨hp,(by decide : 16≤32).trans h32.ge⟩))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h27)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr h49)))

end SymmetricSubgroupAsymptotics.CFSGPSLTwoSmallFieldParameters
