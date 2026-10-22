import SymmetricSubgroupAsymptotics.CFSGSufficientSmallPrimitiveCompression
import SymmetricSubgroupAsymptotics.PrimitiveComponentExhaustionWithoutComposition

/-! Actual complete nonaffine component exhaustion from the sufficient
hybrid, with the existing affine consumer as a separate actual datum.
Every original normal denominator and minimal-block action is retained.
The cutoff64 changes no local margin or final T1 target. -/

/-! Complete primitive degree-nine semisimple source without C336.
The actual quotient has order at most eight. Orders at most seven use
regular compression; noncyclic abelian order eight uses a six-point action;
cyclic and nonabelian order eight use their complete source estimates. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

def primitiveDegreeNine_semisimpleSource_of_sufficient
    {i : PreE7NonPairActionClass 9}
    (D : PrimitiveSocleRawStructure.NonaffineData (preE7NonPairAction 9 i) (Fin 9))
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hOuter : SemisimpleOuterFactorPermutationBound) :
    PreE7RankTailOwnerSourceData 9 i := by
  apply Classical.choice
  let E := finiteGroupSocle (preE7NonPairAction 9 i)
  have hq := D.degreeNine_quotient_card_le_eight_of_sufficient hindex
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


/-! The actual degree-nine full socle has a faithful quotient action of
degree at most eight. This strict local reduction supplies the original
minimal-block compression whenever the original action has at least two
blocks, without any local parity loss or primitive catalogue. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

def NonaffineData.degreeNine_strictCompression_of_sufficient
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X) (hX : Nat.card X = 9)
    (hindex : SufficientSimpleIndexBounds) :
    LocalSemisimpleStrictCompressionData G (Nat.card X) where
  E := finiteGroupSocle G
  chart := D.chart
  quotientDegree := Nat.card (G ⧸ finiteGroupSocle G)
  quotientDegree_pos := Nat.card_pos
  quotientAction := OuterWreathPermutationCompression.regularAction _
  quotientAction_injective := OuterWreathPermutationCompression.regularAction_injective _
  degree_bound := by rw [hX]; decide
  quotientDegree_gap := by
    have hq := D.degreeNine_quotient_card_le_eight_of_card_of_sufficient hX hindex
    rw [hX]
    omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure


/-! Primitive-component exhaustion from actual socle charts and sufficient
compression margins, with no C336 correspondence. Degree9 keeps the
complete actual normal-quotient source in the primitive branch and the
strict many-block comparator in the imprimitive branch. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveSocleRawStructure
open PrimitiveAffineImprimitiveBlockTransfer

def primitiveComponentExhaustion_of_sufficient
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hindex : SufficientSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (affine : PreE7PrimitiveAffineConsumerData) :
    PreE7PrimitiveComponentExhaustionData where
  small := preE7WidthFourSourceOrYonedaTop
  primitive := by
    intro w U hw hp
    letI : Nontrivial (Fin w) := Fin.nontrivial_iff_two_le.mpr (by omega)
    letI : MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w) := hp
    cases Classical.choice (publishedONanScottStructure (preE7NonPairAction w U) (Fin w)) with
    | inr P => exact .inr (affine.primitive w U hw hp P)
    | inl D =>
        by_cases h9 : w=9
        · subst w
          exact .inr (.inl (primitiveDegreeNine_semisimpleSource_of_sufficient
            D hindex hZmud lit hOuter))
        by_cases h30 : 64≤w
        · let C : PreE7PrimitiveLocalMarginData w U := {
            width_lower := hw
            compression := by
              simpa only [Nat.card_fin] using D.sufficientLargeCompression hindex
                (by simpa only [Nat.card_fin] using h30) }
          exact .inr (.inl (C.toSemisimpleMarginData.toRankTailOwnerSource hOuter))
        · let C : PreE7PrimitiveLocalRoundingData w U := {
            width_lower := hw
            compression := by
              by_cases h27 : 27 ≤ w
              · simpa only [Nat.card_fin] using
                  D.sufficientRoundingCompression_twentySevenToSixtyThree hindex
                    (by simpa only [Nat.card_fin] using h27)
                    (by simpa only [Nat.card_fin] using (show w ≤ 63 by omega))
              · simpa only [Nat.card_fin] using D.smallNonNineRoundingCompression_of_sufficient
                  hindex published8 (by simpa only [Nat.card_fin] using hw)
                  (by simpa only [Nat.card_fin] using (show w < 27 by omega))
                  (by simpa only [Nat.card_fin] using h9) }
          exact .inr (.inl (C.toSemisimpleMarginData.toRankTailOwnerSource hOuter))
  imprimitive := by
    intro w U hw basePoint block
    letI : Nontrivial block.Fibre := Finite.one_lt_card_iff_nontrivial.mp (by
      have := block.degrees_ge_two.1
      omega)
    letI : MulAction.IsPreprimitive block.Component block.Fibre := block.component_preprimitive
    cases Classical.choice (publishedONanScottStructure block.Component block.Fibre) with
    | inr P => exact .inr (affine.imprimitive w U hw basePoint block P)
    | inl D =>
        have hf : 5≤Nat.card block.Fibre := D.degree_five_le_of_sufficient hindex
        by_cases h9 : Nat.card block.Fibre=9
        · let C : PreE7OriginalMinimalBlockLocalStrictManyData w U := {
            width_lower := hw
            basePoint := basePoint
            block := block
            compression := D.degreeNine_strictCompression_of_sufficient h9 hindex
            blockCount_two_le := by
              simpa only [Nat.card_eq_fintype_card] using block.degrees_ge_two.2 }
          exact .inr (.inl (C.toSemisimpleMarginData.toRankTailOwnerSource hOuter))
        by_cases h30 : 64≤Nat.card block.Fibre
        · let C : PreE7OriginalMinimalBlockLocalMarginData w U := {
            width_lower := hw
            basePoint := basePoint
            block := block
            compression := D.sufficientLargeCompression hindex h30 }
          exact .inr (.inl (C.toSemisimpleMarginData.toRankTailOwnerSource hOuter))
        · let C : PreE7OriginalMinimalBlockLocalRoundingData w U := {
            width_lower := hw
            basePoint := basePoint
            block := block
            compression := by
              by_cases h27 : 27 ≤ Nat.card block.Fibre
              · exact D.sufficientRoundingCompression_twentySevenToSixtyThree hindex h27 (by omega)
              · exact D.smallNonNineRoundingCompression_of_sufficient hindex published8 hf (by omega) h9 }
          exact .inr (.inl (C.toSemisimpleMarginData.toRankTailOwnerSource hOuter))

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
