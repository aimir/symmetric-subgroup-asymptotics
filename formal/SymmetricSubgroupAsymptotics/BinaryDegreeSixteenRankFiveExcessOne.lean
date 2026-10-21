import SymmetricSubgroupAsymptotics.RDTNormalFSixteenExcessOneRank

/-! The proved proper-normal saving identifies excess one directly from
the ordinary rank of the actual sixteen-point source. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open MarkedC4 MarkedC4.RDTExcessStructure

theorem binary_degree_sixteen_hasExcess_one_of_genRank_five
    (G : Subgroup (Equiv.Perm (Fin 16))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 16, ∃ g : G, g.val x = y)
    (hrank : genRank G = 5) : HasExcess G 16 1 := by
  letI rankFiveExcessOne_originalTransitive : MulAction.IsPretransitive G (Fin 16) := ⟨htrans⟩
  letI rankFiveExcessOne_nilpotent : Group.IsNilpotent G := hG.isNilpotent
  have hwhole : normalGen (⊤ : Subgroup G) = 5 := by
    rw [ActualExcessOneQuotientRank.normalGen_top_eq_genRank G, hrank]
  constructor
  · exact ⟨⊤, inferInstance, by norm_num [hwhole]⟩
  · intro N hN
    letI rankFiveExcessOne_normal : N.Normal := hN
    by_cases heq : N = ⊤
    · rw [heq, hwhole]
      norm_num
    · have hsmall : normalGen N ≤ 4 := by
        by_contra hn
        have hlarge := twoGroup_degree_sixteen_six_le_genRank_of_proper_normal_five
          G hG (Nat.card_fin 16) N heq (by omega)
        omega
      norm_num only [Nat.cast_ofNat, show (16 : ℝ) / 4 + 1 = 5 by norm_num]
      exact (by exact_mod_cast hsmall : (normalGen N : ℝ) ≤ 4).trans (by norm_num)

end SymmetricSubgroupAsymptotics
