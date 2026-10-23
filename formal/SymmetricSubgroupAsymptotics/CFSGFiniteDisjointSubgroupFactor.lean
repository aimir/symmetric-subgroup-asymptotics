import SymmetricSubgroupAsymptotics.CFSGDisjointSubgroupProductCard
import Mathlib.SetTheory.Cardinal.Finite

/-! Finite cardinality turns a disjoint subgroup product into a genuine
unique factorization. No normality or collecting hypothesis is needed. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGFiniteDisjointSubgroupFactor
variable {G : Type*} [Group G] [Finite G]

theorem product_bijective (P Q : Subgroup G) (hPQ : P ⊓ Q = ⊥)
    (hcard : Nat.card G ≤ Nat.card P * Nat.card Q) :
    Function.Bijective (fun z : P × Q => (z.1.val : G) * z.2.val) := by
  apply (CFSGDisjointSubgroupProductCard.product_injective P Q hPQ).bijective_of_nat_card_le
  simpa only [Nat.card_prod] using hcard

theorem exists_unique_factors (P Q : Subgroup G) (hPQ : P ⊓ Q = ⊥)
    (hcard : Nat.card G ≤ Nat.card P * Nat.card Q) (g : G) :
    ∃! z : P × Q, (z.1.val : G) * z.2.val = g :=
  (product_bijective P Q hPQ hcard).existsUnique g

end SymmetricSubgroupAsymptotics.CFSGFiniteDisjointSubgroupFactor
