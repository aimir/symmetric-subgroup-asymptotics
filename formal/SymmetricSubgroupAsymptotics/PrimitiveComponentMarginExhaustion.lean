import SymmetricSubgroupAsymptotics.PrimitiveSemisimpleTwoThirdsCompression
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import SymmetricSubgroupAsymptotics.Non2PreE7PrimitiveBlockExhaustion
import SymmetricSubgroupAsymptotics.PrimitiveCatalogueClassificationAssembly
import SymmetricSubgroupAsymptotics.Non2PreE7SmallWidthMenu

/-! Standalone primitive-component exhaustion with the actual two-thirds
semisimple comparator. The existing affine consumer is retained unchanged.
Neither the116-row correspondence nor the stronger half-degree bound is a
premise. Original minimal blocks and their literal wreath quotient survive
the imprimitive branch. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveSocleRawStructure
open PrimitiveAffineImprimitiveBlockTransfer

def primitiveComponentExhaustion_of_composition_and_margin
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (hindex : PublishedSimpleIndexBounds)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (affine : PreE7PrimitiveAffineConsumerData) :
    PreE7PrimitiveComponentExhaustionData where
  small := preE7WidthFourSourceOrYonedaTop
  primitive := by
    intro w U hw hp
    letI : Nontrivial (Fin w) := Fin.nontrivial_iff_two_le.mpr (by omega)
    letI : MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w) := hp
    cases Classical.choice (publishedONanScottStructure (preE7NonPairAction w U) (Fin w)) with
    | inl D =>
        let C : PreE7PrimitiveLocalMarginData w U := {
          width_lower := hw
          compression := by
            simpa only [Nat.card_fin] using
              D.twoThirdsCompression catalogue published8 published16 hindex (by simpa using hw) }
        exact .inr (.inl (C.toSemisimpleMarginData.toRankTailOwnerSource hOuter))
    | inr P => exact .inr (affine.primitive w U hw hp P)
  imprimitive := by
    intro w U hw basePoint block
    letI : Nontrivial block.Fibre := Finite.one_lt_card_iff_nontrivial.mp (by
      have := block.degrees_ge_two.1
      omega)
    letI : MulAction.IsPreprimitive block.Component block.Fibre := block.component_preprimitive
    cases Classical.choice (publishedONanScottStructure block.Component block.Fibre) with
    | inl D =>
        let C : PreE7OriginalMinimalBlockLocalMarginData w U := {
          width_lower := hw
          basePoint := basePoint
          block := block
          compression := D.twoThirdsCompression catalogue published8 published16 hindex
            (D.degree_five_le_of_simpleIndex hindex) }
        exact .inr (.inl (C.toSemisimpleMarginData.toRankTailOwnerSource hOuter))
    | inr P => exact .inr (affine.imprimitive w U hw basePoint block P)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
