import SymmetricSubgroupAsymptotics.NinePointCyclicSylowSocleQuotient
import SymmetricSubgroupAsymptotics.PrimitiveSocleBelowTwentyFiveSingleFactorWithoutIndexInput
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawOneFactor
import SymmetricSubgroupAsymptotics.CFSGSporadicGeneration

/-! The actual displayed pairs of twenty models discharge the head
internally in the cyclic Sylow9 branch. No finite model/outer callback or
new universal generator assertion is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NinePointCyclicSylowDisplayedSporadicPair
open PrimitiveSocleRawStructure
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem genRank_le_four {G : Type} [Group G] [Finite G]
    [MulAction G (Fin 9)] [FaithfulSMul G (Fin 9)]
    (D : NonaffineData G (Fin 9)) (s : CFSG.Sporadic)
    (hs : ¬CFSGGeneration.SporadicGenerationResidual s) (e : D.Simple ≃* s.Model)
    (P : Sylow 3 (finiteGroupSocle G)) [IsCyclic P] (hP : Nat.card P=9) :
    MarkedC4.genRank G≤4 := by
  have hk := PrimitiveSocleBelowTwentyFiveSingleFactorWithoutIndexInput.factorCount_eq_one
    D (by simp only [Nat.card_fin]; decide)
  let S := finiteGroupSocle G
  let eS := D.oneFactorEquiv hk
  letI : IsSimpleGroup S := eS.isSimpleGroup
  letI : MulAction.IsPretransitive S (Fin 9) := D.socle_transitive
  have hn : ¬IsMulCommutative S := by
    intro hh
    apply D.noncommutative
    apply IsMulCommutative.of_comm
    intro a b
    have he := congrArg eS (hh.is_comm.comm (eS.symm a) (eS.symm b))
    simpa only [map_mul,eS.apply_symm_apply] using he
  obtain ⟨U,hgen,hcard⟩ := CFSGGeneration.twoGenerated_of_mulEquiv_sporadic s hs (eS.trans e)
  exact NinePointCyclicSylowSocleQuotient.genRank_le_four_of_simple_rank_le_two
    S hn P hP ((MarkedC4.genRank_le hgen).trans hcard)

end SymmetricSubgroupAsymptotics.NinePointCyclicSylowDisplayedSporadicPair
