import SymmetricSubgroupAsymptotics.RDTNormalFSixteenRankSix
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenExcessProfile

/-! The exact degree-sixteen excess-two part of RDT5.7. The maximum in
HasExcess can be attained by a proper original normal; that case is
transported to the original source rank before invoking the five templates.
No excess theorem or classification premise is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open MarkedC4 MarkedC4.RDTExcessStructure

theorem degree_sixteen_excess_two_six_le_genRank
    (G : Subgroup (Equiv.Perm (Fin 16))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 16, ∃ g : G, g.val x = y)
    (hexcess : HasExcess G 16 2) : 6 ≤ genRank G := by
  letI : MulAction.IsPretransitive G (Fin 16) := ⟨htrans⟩
  obtain ⟨V, hV, hval⟩ := hexcess.1
  letI := hV
  have hnormal : normalGen V = 6 := by
    norm_num at hval
    exact_mod_cast hval
  by_cases htop : V = ⊤
  · rw [htop] at hnormal
    have h := ActualExcessOneQuotientRank.normalGen_top_le_genRank G
    omega
  · exact twoGroup_degree_sixteen_six_le_genRank_of_proper_normal_five G hG
      (by simp only [Nat.card_fin]) V htop (by omega)

theorem theorem57_degree_sixteen_excess_two
    (G : Subgroup (Equiv.Perm (Fin 16))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 16, ∃ g : G, g.val x = y)
    (hexcess : HasExcess G 16 2)
    (N : Subgroup G) [N.Normal]
    (hnonab : ¬ ∀ a b : G ⧸ N, a * b = b * a) :
    ∃ V : Subgroup (G ⧸ N), V.Normal ∧
      ActualNormalFMarkedPeel.commutatorLog V +
        (5 / 4 : ℝ) * ActualNormalFMarkedPeel.centralLog V ≤ 8 ∧
      ActualNormalFMarkedPeel.centralLog V ≤ 4 := by
  letI : MulAction.IsPretransitive G (Fin 16) := ⟨htrans⟩
  obtain ⟨F⟩ := transitiveBinaryPairFrame_nonempty 3 G hG
    (by simp only [Nat.card_fin]; decide)
  exact F.sixteen_rank_six_all_normal_quotients hG
    (degree_sixteen_excess_two_six_le_genRank G hG htrans hexcess) N hnonab

end SymmetricSubgroupAsymptotics
