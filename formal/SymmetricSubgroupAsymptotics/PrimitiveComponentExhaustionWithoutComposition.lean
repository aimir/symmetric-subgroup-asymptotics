import SymmetricSubgroupAsymptotics.PrimitiveLargeSemisimpleCompressionWithoutCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveSmallNonNineRoundingCompression
import SymmetricSubgroupAsymptotics.PrimitiveDegreeNineSemisimpleSource
import SymmetricSubgroupAsymptotics.PrimitiveDegreeNineStrictManyCompression
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import SymmetricSubgroupAsymptotics.Non2PreE7PrimitiveBlockExhaustion
import SymmetricSubgroupAsymptotics.PrimitiveCatalogueClassificationAssembly
import SymmetricSubgroupAsymptotics.Non2PreE7SmallWidthMenu

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

def primitiveComponentExhaustion_without_composition
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hindex : PublishedSimpleIndexBounds)
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
          exact .inr (.inl (primitiveDegreeNine_semisimpleSource_without_catalogue
            D hindex hZmud lit hOuter))
        by_cases h30 : 30≤w
        · let C : PreE7PrimitiveLocalMarginData w U := {
            width_lower := hw
            compression := by
              simpa only [Nat.card_fin] using D.largeTwoThirdsCompression hindex
                (by simpa only [Nat.card_fin] using h30) }
          exact .inr (.inl (C.toSemisimpleMarginData.toRankTailOwnerSource hOuter))
        · let C : PreE7PrimitiveLocalRoundingData w U := {
            width_lower := hw
            compression := by
              simpa only [Nat.card_fin] using D.smallNonNineRoundingCompression
                hindex published8 (by simpa only [Nat.card_fin] using hw)
                (by simpa only [Nat.card_fin] using lt_of_not_ge h30)
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
        have hf : 5≤Nat.card block.Fibre := D.degree_five_le_of_simpleIndex hindex
        by_cases h9 : Nat.card block.Fibre=9
        · let C : PreE7OriginalMinimalBlockLocalStrictManyData w U := {
            width_lower := hw
            basePoint := basePoint
            block := block
            compression := D.degreeNine_strictCompression h9 hindex
            blockCount_two_le := by
              simpa only [Nat.card_eq_fintype_card] using block.degrees_ge_two.2 }
          exact .inr (.inl (C.toSemisimpleMarginData.toRankTailOwnerSource hOuter))
        by_cases h30 : 30≤Nat.card block.Fibre
        · let C : PreE7OriginalMinimalBlockLocalMarginData w U := {
            width_lower := hw
            basePoint := basePoint
            block := block
            compression := D.largeTwoThirdsCompression hindex h30 }
          exact .inr (.inl (C.toSemisimpleMarginData.toRankTailOwnerSource hOuter))
        · let C : PreE7OriginalMinimalBlockLocalRoundingData w U := {
            width_lower := hw
            basePoint := basePoint
            block := block
            compression := D.smallNonNineRoundingCompression hindex published8 hf
              (lt_of_not_ge h30) h9 }
          exact .inr (.inl (C.toSemisimpleMarginData.toRankTailOwnerSource hOuter))

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
