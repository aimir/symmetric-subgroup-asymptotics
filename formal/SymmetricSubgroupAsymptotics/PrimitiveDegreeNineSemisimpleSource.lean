import SymmetricSubgroupAsymptotics.PrimitiveDegreeNineQuotientOrderEight
import SymmetricSubgroupAsymptotics.PrimitiveNineNonabelianEightMixedSource
import SymmetricSubgroupAsymptotics.PrimitiveNineCyclicEightSource
import SymmetricSubgroupAsymptotics.SmallAbelianQuotientPermutationSix

/-! Complete primitive degree-nine semisimple source without C336.
The actual quotient has order at most eight. Orders at most seven use
regular compression; noncyclic abelian order eight uses a six-point action;
cyclic and nonabelian order eight use their complete source estimates. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

def primitiveDegreeNine_semisimpleSource_without_catalogue
    {i : PreE7NonPairActionClass 9}
    (D : PrimitiveSocleRawStructure.NonaffineData (preE7NonPairAction 9 i) (Fin 9))
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hOuter : SemisimpleOuterFactorPermutationBound) :
    PreE7RankTailOwnerSourceData 9 i := by
  apply Classical.choice
  let E := finiteGroupSocle (preE7NonPairAction 9 i)
  have hq := D.degreeNine_quotient_card_le_eight hindex
  change Nat.card (preE7NonPairAction 9 i ⧸ E) ≤ 8 at hq
  by_cases h8 : Nat.card (preE7NonPairAction 9 i ⧸ E) = 8
  · by_cases hc : IsMulCommutative (preE7NonPairAction 9 i ⧸ E)
    · by_cases hcyc : IsCyclic (preE7NonPairAction 9 i ⧸ E)
      · letI := hcyc
        exact ⟨PrimitiveNineCyclicEightSource.toRankTailOwnerSource E D.chart h8
          lit.kovacsPraeger hOuter⟩
      · letI := hc
        obtain ⟨d,hd,hd6,f,hf⟩ := smallAbelian_noncyclic_faithful_permutation_six
          (Or.inl h8) hcyc
        let M : PreE7SemisimpleMarginData 9 i := {
          width_lower := by decide
          E := E
          chart := D.chart
          quotientDegree := d
          quotientAction := f
          quotientAction_injective := hf
          quotientDegree_margin := PreE7SemisimpleMarginData.margin_of_rounding_gap
            (by decide : 9 ≤ 1024) (by
              have he : evenWidth 9 = 8 := by decide
              rw [he]
              omega) }
        exact ⟨M.toRankTailOwnerSource hOuter⟩
    · exact ⟨PrimitiveNineNonabelianEightMixedSource.toRankTailOwnerSource E D.chart h8 hc
        hZmud lit hOuter⟩
  · let M : PreE7SemisimpleMarginData 9 i := {
      width_lower := by decide
      E := E
      chart := D.chart
      quotientDegree := Nat.card (preE7NonPairAction 9 i ⧸ E)
      quotientAction := OuterWreathPermutationCompression.regularAction _
      quotientAction_injective := OuterWreathPermutationCompression.regularAction_injective _
      quotientDegree_margin := PreE7SemisimpleMarginData.margin_of_rounding_gap
        (by decide : 9 ≤ 1024) (by
          have he : evenWidth 9 = 8 := by decide
          rw [he]
          omega) }
    exact ⟨M.toRankTailOwnerSource hOuter⟩

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
