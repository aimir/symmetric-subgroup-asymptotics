import Mathlib.GroupTheory.Index

set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.NormalSubgroupCoprimeIndexContainment

/-- The actual subgroup has trivial image in a coprime normal quotient. -/
theorem le_of_coprime_card_index {G : Type*} [Group G]
    (P H : Subgroup G) [H.Normal]
    (hcop : (Nat.card P).Coprime H.index) : P ≤ H := by
  rw [← Subgroup.relIndex_eq_one]
  exact Nat.eq_one_of_dvd_coprimes hcop (Subgroup.relIndex_dvd_card H P)
    (H.relIndex_dvd_index_of_normal P)

end SymmetricSubgroupAsymptotics.NormalSubgroupCoprimeIndexContainment
