import SymmetricSubgroupAsymptotics.BinaryTransitiveAbelianizationQuarterPlusTwo
import SymmetricSubgroupAsymptotics.PrimeIndexNormalAbelianizationLower

/-! A literal index-two original normal of rank nine saturates the full
original degree-thirty-two abelianization order. Higher cyclic factors
are retained until an independent original-lift carry proof eliminates them. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- The lower bound is for this actual N, not for an enlarged maximal
normal with an unproved normal-rank monotonicity assertion. -/
theorem binary_degree_thirty_two_abelianization_card_of_index_two_normal_nine
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 32) (N : Subgroup U) [N.Normal]
    (hindex : N.index = 2) (hN : 9 ≤ MarkedC4.normalGen N) :
    Nat.card (Abelianization U) = 1024 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hupper := twoGroup_transitive_abelianization_card_le_quarter_add_two U hU
  rw [hdegree] at hupper
  norm_num at hupper
  have hlower := pGroup_normalGen_prime_index_le_abelianization_card 2 hU N hindex
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hN
  norm_num at hp
  nlinarith

end SymmetricSubgroupAsymptotics
