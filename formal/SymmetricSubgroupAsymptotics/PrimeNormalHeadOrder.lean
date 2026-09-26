import SymmetricSubgroupAsymptotics.PrimeNormalHeadCentralizer
import Mathlib.Data.Nat.Log

/-! The complete maximum of original ambient-invariant normal heads is
bounded by the order of the containing subgroup. The subgroup need not
be normal, and the ambient group need not be a p-group. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- The identity centralizer gives an order budget for the maximum over
ALL original G-normal subgroups contained in S. -/
theorem primeNormalHeadMax_pow_le_card (S : Subgroup G) :
    p ^ primeNormalHeadMax p S ≤ Nat.card S :=
  (primeNormalHeadMax_pow_le_centralizer_card p S 1).trans
    (Subgroup.card_le_of_le inf_le_left)

/-- The natural logarithm is a floor bound; no prime-power order or
numerical normal-head premise is required. -/
theorem primeNormalHeadMax_le_log_card (S : Subgroup G) :
    primeNormalHeadMax p S ≤ Nat.log p (Nat.card S) :=
  Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt
    (primeNormalHeadMax_pow_le_card p S)

end SymmetricSubgroupAsymptotics
