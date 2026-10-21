import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoElementaryExcessOneNormalF
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoWideKernelUnitPacket
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoExcessProfile

/-! Exact two-sector boundary of the remaining excess-one proof. The
elementary top and the wide rank-six top are already proved. The two
critical clauses below are internal proof obligations, not new published
inputs and not discharged merely by this reduction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open MarkedC4 MarkedC4.RDTExcessStructure MarkedC4.ActualNormalFMarkedPeel

def BinaryThirtyTwoCriticalHeadTopNormalF (h t : ℕ) : Prop :=
  ∀ (G : Subgroup (Equiv.Perm (Fin 32))) (_hG : IsPGroup 2 G)
    [MulAction.IsPretransitive G (Fin 32)]
    (F : BinaryPairFrame G (Fin 16)),
    genRank G=9 → normalGen F.top.ker=h → genRank F.top.range=t →
    ∀ (N : Subgroup G) [N.Normal],N≤commutator G →
    (¬∀ a b : G ⧸ N,a*b=b*a) →
    ∃ V : Subgroup (G ⧸ N),V.Normal ∧
      commutatorLog V+centralLog V≤16 ∧ centralLog V≤8

theorem rank_nine_thirty_two_normalF_of_critical_clauses
    (h36 : BinaryThirtyTwoCriticalHeadTopNormalF 3 6)
    (h45 : BinaryThirtyTwoCriticalHeadTopNormalF 4 5)
    (G : Subgroup (Equiv.Perm (Fin 32))) (hG : IsPGroup 2 G)
    [MulAction.IsPretransitive G (Fin 32)] (hrank : genRank G=9)
    (N : Subgroup G) [N.Normal] (hN : N≤commutator G)
    (hnonab : ¬∀ a b : G ⧸ N,a*b=b*a) :
    ∃ V : Subgroup (G ⧸ N),V.Normal ∧
      commutatorLog V+centralLog V≤16 ∧ centralLog V≤8 := by
  have hexists : Nonempty (BinaryPairFrame G (Fin 16)) :=
    transitiveBinaryPairFrame_nonempty 4 G hG (by norm_num only [Nat.card_fin])
  obtain ⟨F⟩ := hexists
  by_cases hpow : ∀ t : F.top.range,t^2=1
  · exact F.elementary_rank_nine_all_normalF_packet hG hrank hpow N hnonab
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hTop := F.top_isPGroup hG
  letI : Group.IsNilpotent F.top.range := hTop.isNilpotent
  have hk : normalGen F.top.ker≤4 := by
    have hh := twoGroup_faithful_permutationSubrepresentationHead_le_quarter hTop hpow
      (F.axisNaturalSubrepresentation F.top.ker)
    rw [representationHead_finrank_eq_coinvariants,←F.axisNatural_normalGen F.top.ker le_rfl hG] at hh
    norm_num only [Nat.card_fin] at hh
    exact hh
  have htop : genRank F.top.range≤6 := by
    have ht := twoGroup_transitive_normalGen_le_quarter_add_two F.top.range hTop (⊤ : Subgroup F.top.range)
    norm_num only [Nat.card_fin] at ht
    exact (genRank_le_normalGen_top (G := F.top.range)).trans ht
  have hg : genRank G≤normalGen F.top.ker+genRank F.top.range := by
    letI : IsMulCommutative F.top.ker := ⟨⟨fun a b => F.bitsHom_injective (by
      rw [map_mul,map_mul,mul_comm])⟩⟩
    letI : IsMulCommutative F.top.rangeRestrict.ker := by
      rw [MonoidHom.ker_rangeRestrict]
      infer_instance
    have hh := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
      F.top.rangeRestrict F.top.rangeRestrict_surjective
    rw [MonoidHom.ker_rangeRestrict] at hh
    omega
  by_cases hsix : 6≤genRank F.top.range
  · by_cases hwide : 4≤normalGen F.top.ker
    · exact F.rank_nine_rank_six_top_wide_kernel_all_normal_unit hG hrank hsix hwide N hnonab
    · have hthree : normalGen F.top.ker=3 := by omega
      have hsixEq : genRank F.top.range=6 := by omega
      exact h36 G hG F hrank hthree hsixEq N hN hnonab
  · have hfour : normalGen F.top.ker=4 := by omega
    have hfive : genRank F.top.range=5 := by omega
    exact h45 G hG F hrank hfour hfive N hN hnonab

theorem theorem57_degree_thirty_two_excess_one_of_critical_clauses
    (h36 : BinaryThirtyTwoCriticalHeadTopNormalF 3 6)
    (h45 : BinaryThirtyTwoCriticalHeadTopNormalF 4 5)
    (G : Subgroup (Equiv.Perm (Fin 32))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 32,∃ g : G,g.val x=y)
    (hexcess : HasExcess G 32 1)
    (N : Subgroup G) [N.Normal] (hnonab : ¬∀ a b : G ⧸ N,a*b=b*a)
    (hquot : genRank (G ⧸ N)=genRank G) :
    ∃ V : Subgroup (G ⧸ N),V.Normal ∧
      commutatorLog V+centralLog V≤16 ∧ centralLog V≤8 := by
  letI : MulAction.IsPretransitive G (Fin 32) := ⟨htrans⟩
  letI : Group.IsNilpotent G := hG.isNilpotent
  obtain ⟨W,hW,hw⟩ := hexcess.1
  letI := hW
  have hhigh : (32 : ℝ)/4<(normalGen W : ℝ) := by
    have hwNat : normalGen W=9 := by norm_num at hw;exact_mod_cast hw
    norm_num [hwNat]
  have hwhole := BinaryDegreeThirtyTwoExcessProfile.only_whole_of_excess_one G hG htrans hexcess W hhigh
  rw [hwhole,MarkedC4.ActualExcessOneQuotientRank.normalGen_top_eq_genRank G] at hw
  have hrank : genRank G=9 := by norm_num at hw;exact_mod_cast hw
  exact rank_nine_thirty_two_normalF_of_critical_clauses h36 h45 G hG hrank N
    (binary_degree_thirty_two_rank_nine_denominator_le_commutator G hG
      (by simp only [Nat.card_fin]) hrank N hquot) hnonab

end SymmetricSubgroupAsymptotics
