import SymmetricSubgroupAsymptotics.EvenPermutationTwicePrimeOrderDegree
import Mathlib.GroupTheory.IsPerfect

/-! Every permutation image of an actual perfect group has sign1.
Injectivity preserves the selected original element's order, so the
sign-aware cycle-support bound applies without a model-order assumption. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PerfectPermutationTwicePrimeOrderDegree

variable {G X : Type*} [Group G] [Group.IsPerfect G] [Fintype X] [DecidableEq X]

theorem prime_add_four_le_card_of_faithful_action (f : G →* Equiv.Perm X)
    (hf : Function.Injective f) (g : G) (p : ℕ) (hp : p.Prime)
    (hcop : Nat.Coprime 2 p) (hdiv : 2*p ∣ orderOf g) : p+4 ≤ Nat.card X := by
  have hsign : Equiv.Perm.sign (f g) = 1 :=
    Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp f)
      (Group.IsPerfect.mem_commutator (g := g))
  apply EvenPermutationTwicePrimeOrderDegree.prime_add_four_le_card_of_twice_prime_dvd_orderOf
    (f g) hsign p hp hcop
  rw [orderOf_injective f hf g]
  exact hdiv

theorem eleven_le_card_of_faithful_action (f : G →* Equiv.Perm X)
    (hf : Function.Injective f) (g : G) (hdiv : 14 ∣ orderOf g) : 11 ≤ Nat.card X :=
  prime_add_four_le_card_of_faithful_action f hf g 7 (by decide) (by decide) hdiv

end SymmetricSubgroupAsymptotics.PerfectPermutationTwicePrimeOrderDegree
