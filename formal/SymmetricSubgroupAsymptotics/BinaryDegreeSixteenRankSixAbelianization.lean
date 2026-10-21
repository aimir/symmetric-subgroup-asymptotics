import SymmetricSubgroupAsymptotics.PGroupGeneratorAbelianizationOrder
import SymmetricSubgroupAsymptotics.BinaryTransitiveAbelianizationQuarterPlusTwo

/-! The full abelianization of an actual sixteen-point binary source of
rank at least six has order 64. This does not assert exponent two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem binary_degree_sixteen_abelianization_card_of_rank_six
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 16) (hhigh : 6 ≤ MarkedC4.genRank U) :
    Nat.card (Abelianization U) = 64 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hupper := twoGroup_transitive_abelianization_card_le_quarter_add_two U hU
  rw [hdegree] at hupper
  norm_num at hupper
  have hlower := pGroup_pow_genRank_le_abelianization_card 2 hU
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hhigh
  norm_num at hp
  omega

end SymmetricSubgroupAsymptotics
