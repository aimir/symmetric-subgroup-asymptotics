import SymmetricSubgroupAsymptotics.RDTNormalFThirtyTwoCriticalReduction
import SymmetricSubgroupAsymptotics.BinaryPairRegular45RankNineNormalF
import SymmetricSubgroupAsymptotics.BinaryPairRegular46RankNineNormalF
import SymmetricSubgroupAsymptotics.BinaryPairHeisenberg13RankNineNormalF
import SymmetricSubgroupAsymptotics.BinaryPairHeisenbergFourteenRankNineNormalF
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel12

/-! Exact head-three/top-six critical clause. Only the labels of an
actual inner pair frame are reindexed. The original thirty-two points,
outer frame and SAME original normal N≤G′ remain unchanged in every case.
The four actual inner models have closed semantic packets; the fifth
possible high-rank inner kernel is excluded by its proved head-two bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem binaryThirtyTwoCriticalHeadThreeTopSixNormalF_proved :
    BinaryThirtyTwoCriticalHeadTopNormalF 3 6 := by
  intro G hG htrans F hrank hthree hsix N hNormal hND hnonab
  letI : MulAction.IsPretransitive G (Fin 32) := htrans
  letI : N.Normal := hNormal
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hTop := F.top_isPGroup hG
  obtain ⟨E0⟩ := transitiveBinaryPairFrame_nonempty 3 F.top.range hTop
    (by norm_num only [Nat.card_fin])
  rcases E0.six_le_genRank_literal_top_models hTop (by omega) with
    ⟨g,hH,hlarge⟩ | ⟨g,hH,hlarge⟩
  · let E := E0.reindex g
    change 3≤MarkedC4.normalGen E.top.ker at hlarge
    rcases E.regular_large_axis_models hTop E.top.ker le_rfl hH (by omega) with
      ⟨hK,_⟩ | ⟨hK,_⟩
    all_goals rw [E.ambientAxis_kernel] at hK
    · have hJ : E.kernelSpace=(BinaryRegularEightNaturalRegistry.charts 45).2.space := by
        rw [←BinaryRegularEightNaturalRegistry.states_space,
          BinaryRegularEightNaturalRegistry.kernel45_space]
        exact hK
      exact F.regular45_rank_nine_derived_normalF_packet E hG hrank hthree hsix hH hJ N hND hnonab
    · have hJ : E.kernelSpace=(BinaryRegularEightNaturalRegistry.charts 46).2.space := by
        rw [←BinaryRegularEightNaturalRegistry.states_space,
          BinaryRegularEightNaturalRegistry.kernel46_space]
        exact hK
      exact F.regular46_rank_nine_derived_normalF_packet E hG hrank hthree hsix hH hJ N hND hnonab
  · let E := E0.reindex g
    change 2≤MarkedC4.normalGen E.top.ker at hlarge
    rcases E.heisenberg_large_axis_models hTop E.top.ker le_rfl hH (by omega) with
      ⟨hK,_⟩ | ⟨hK,_⟩ | ⟨hK,_⟩
    all_goals rw [E.ambientAxis_kernel] at hK
    · have hJ : E.kernelSpace=(BinaryHeisenbergEightNaturalHeads.charts 12).2.space := by
        rw [←BinaryHeisenbergEightNaturalHeads.states_space,
          BinaryHeisenbergEightNaturalHeads.kernel12_space]
        exact hK
      let W := F.axisNaturalSubrepresentation F.top.ker
      have hb := E.naturalModuleHead_le_of_literal_pair_layer_bound
        BinaryHeisenbergEightNaturalHeads.H hH _ hJ 2
        BinaryPairLayerHead8T22Kernel12.pair_bound W
      change Module.finrank (ZMod 2)
        (F.axisNaturalSubrepresentation F.top.ker).toRepresentation.Coinvariants≤2 at hb
      rw [←F.axisNatural_normalGen F.top.ker le_rfl hG,hthree] at hb
      omega
    · have hJ : E.kernelSpace=(BinaryHeisenbergEightNaturalHeads.charts 13).2.space := by
        rw [←BinaryHeisenbergEightNaturalHeads.states_space,
          BinaryHeisenbergEightNaturalHeads.kernel13_space]
        exact hK
      exact F.heisenberg13_rank_nine_derived_normalF_packet E hG hrank hthree hsix hH hJ N hND hnonab
    · have hJ : E.kernelSpace=(BinaryHeisenbergEightNaturalHeads.charts 14).2.space := by
        rw [←BinaryHeisenbergEightNaturalHeads.states_space,
          BinaryHeisenbergEightNaturalHeads.kernel14_space]
        exact hK
      exact F.heisenberg14_rank_nine_derived_normalF_packet E hG hrank hthree hsix hH hJ N hND hnonab

end SymmetricSubgroupAsymptotics
