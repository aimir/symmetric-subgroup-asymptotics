import SymmetricSubgroupAsymptotics.BinaryProperNormalGapAbelianization
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoProperSaving
import SymmetricSubgroupAsymptotics.PGroupRankPreservingKernelCommutator

/-! The full original degree32 rank-nine source has elementary
abelianization, and every actual rank-preserving normal quotient kills
only original derived elements. Both statements derive their hypotheses
from the checked proper-normal saving, without a degree32 census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X]

/-- The full abelianization, including any initially possible higher
cyclic factors, is proved to have exponent two. -/
theorem binary_degree_thirty_two_rank_nine_abelianization_exponent
    (hU : IsPGroup 2 U) (hdegree : Nat.card X=32)
    (hrank : MarkedC4.genRank U=9) :
    ∀ a : Abelianization U, a^2=1 := by
  apply binary_abelianization_exponent_of_strict_proper_normal_gap hU
  intro N hN hproper
  letI := hN
  have hbound : MarkedC4.normalGen N≤8 := by
    by_contra hlarge
    have hten := twoGroup_degree_thirty_two_ten_le_genRank_of_proper_normal_nine
      U hU hdegree N hproper (by omega)
    omega
  omega

/-- The SAME original denominator of a rank-preserving quotient lies
in the SAME original derived subgroup. -/
theorem binary_degree_thirty_two_rank_nine_denominator_le_commutator
    (hU : IsPGroup 2 U) (hdegree : Nat.card X=32)
    (hrank : MarkedC4.genRank U=9) (N : Subgroup U) [N.Normal]
    (hquot : MarkedC4.genRank (U ⧸ N)=MarkedC4.genRank U) :
    N≤commutator U := by
  have hk := pGroup_kernel_le_commutator_of_rank_preserving_abelianization_exponent
    2 hU (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    (binary_degree_thirty_two_rank_nine_abelianization_exponent U hU hdegree hrank) hquot
  simpa only [QuotientGroup.ker_mk'] using hk

end SymmetricSubgroupAsymptotics
