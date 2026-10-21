import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoRankTenAbelianization
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoProperSaving
import SymmetricSubgroupAsymptotics.MarkedC4RDTExcessStructure

/-! The exact excess-two interface gives rank ten for the original
whole degree32 source, even if its displayed excessive normal is proper.
The full original abelianization is then elementary by its order budget. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open MarkedC4 MarkedC4.RDTExcessStructure
local instance rankTenExcessTwoFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem binary_degree_thirty_two_excess_two_genRank_eq_ten
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X=32) (hexcess : HasExcess U 32 2) : genRank U=10 := by
  letI : Group.IsNilpotent U := hU.isNilpotent
  have hupper := hexcess.2 (⊤ : Subgroup U) inferInstance
  rw [MarkedC4.ActualExcessOneQuotientRank.normalGen_top_eq_genRank U] at hupper
  norm_num at hupper
  have hu : genRank U≤10 := by exact_mod_cast hupper
  obtain ⟨N,hN,hval⟩ := hexcess.1
  letI := hN
  norm_num at hval
  have hv : normalGen N=10 := by exact_mod_cast hval
  have hl : 10≤genRank U := by
    by_cases htop : N=⊤
    · rw [htop,MarkedC4.ActualExcessOneQuotientRank.normalGen_top_eq_genRank U] at hv
      omega
    · exact twoGroup_degree_thirty_two_ten_le_genRank_of_proper_normal_nine
        U hU hdegree N htop (by omega)
  omega

theorem binary_degree_thirty_two_excess_two_abelianization_exponent
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X=32) (hexcess : HasExcess U 32 2) :
    ∀ a : Abelianization U, a^2=1 :=
  binary_degree_thirty_two_rank_ten_abelianization_exponent U hU hdegree
    (binary_degree_thirty_two_excess_two_genRank_eq_ten U hU hdegree hexcess)

end SymmetricSubgroupAsymptotics
