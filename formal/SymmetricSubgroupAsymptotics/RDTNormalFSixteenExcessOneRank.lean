import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenExcessProfile

/-! The excess-one rank is the rank of the original whole group. No
published excess classification or detached quotient rank is substituted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open MarkedC4 MarkedC4.RDTExcessStructure

theorem degree_sixteen_excess_one_genRank_eq_five
    (G : Subgroup (Equiv.Perm (Fin 16))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 16, ∃ g : G, g.val x = y)
    (hexcess : HasExcess G 16 1) : genRank G = 5 := by
  letI : Group.IsNilpotent G := hG.isNilpotent
  obtain ⟨V, hV, hval⟩ := hexcess.1
  letI := hV
  have hn : normalGen V = 5 := by
    norm_num at hval
    exact_mod_cast hval
  have hv : V = ⊤ := BinaryDegreeSixteenExcessProfile.only_whole_of_excess_one
    G hG htrans hexcess V (by norm_num [hn])
  rw [hv, ActualExcessOneQuotientRank.normalGen_top_eq_genRank] at hval
  norm_num at hval
  exact_mod_cast hval

end SymmetricSubgroupAsymptotics
