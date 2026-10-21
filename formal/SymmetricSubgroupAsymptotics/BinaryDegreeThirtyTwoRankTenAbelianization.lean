import SymmetricSubgroupAsymptotics.PGroupAbelianizationExponentOfOrder
import SymmetricSubgroupAsymptotics.BinaryTransitiveAbelianizationQuarterPlusTwo

/-! A rank-ten original degree32 source saturates the complete
abelianization order budget, so its full abelianization is elementary.
This statement requires neither a zero outer model nor carry choices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem binary_degree_thirty_two_rank_ten_abelianization_exponent
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X=32) (hrank : MarkedC4.genRank U=10) :
    ∀ a : Abelianization U, a^2=1 := by
  apply pGroup_abelianization_exponent_of_card_le_pow_genRank 2 hU
  have hc := twoGroup_transitive_abelianization_card_le_quarter_add_two U hU
  rw [hdegree] at hc
  norm_num at hc
  simpa only [hrank] using hc

end SymmetricSubgroupAsymptotics
