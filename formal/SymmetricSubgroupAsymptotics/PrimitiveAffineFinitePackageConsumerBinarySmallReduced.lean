import SymmetricSubgroupAsymptotics.PrimitiveAffineFinitePackageConsumer
import SymmetricSubgroupAsymptotics.BinaryAffineSmallCatalogueBridge
import SymmetricSubgroupAsymptotics.PrimitiveAffineLowDegreeConsumerAssemblyBinarySmallReduced
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveComponentSourceAssemblyBinarySmallReduced

/-! Isolated binary-small consumer route. Original datatypes, interfaces,
and finite certificate declarations are imported unchanged. Only the
changed consumer declarations and their private helper closure are copied. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

namespace BinarySmallReduced

open PrimitiveAffineImprimitiveBlockTransfer

def preE7PrimitiveAffineConsumerData_of_finitePackage
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hcomp : PrimitiveCompositionLengthInput)
    (hKP : KovacsPraegerAbelianizationBound)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (publishedSmall : BinaryAffineSmallCatalogueData)
    (publishedFinite : PublishedPrimitiveAffineFiniteInput)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (publishedPairs : PublishedDegreeTwoFourPairClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (degreeTwo : PrimitiveAffineResidualDegreeSource 2) :
    PreE7PrimitiveAffineConsumerData := by
  let exceptional := _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.BinarySmallReduced.preE7PrimitiveAffineExceptionalCellConsumerData_of_degreeTwoSource
    hZmud lit hgen hClifford hKP hMN hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm hSimpleGen publishedSmall publishedSix publishedPairs published8
    published16 socle degreeTwo
  let components := _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.preE7PrimitiveAffineImprimitiveComponentSourceData publishedSmall
    hcomp hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm exceptional
  refine { primitive := ?_, imprimitive := ?_ }
  · intro w U hw hprimitive P
    exact .inl (publishedFinite.primitiveOwner hcomp hgen hKP U hw hprimitive P)
  · intro w U hw basePoint block P
    exact match components.source w U hw basePoint block P with
    | .inl source => imprimitiveAffineComponentTransfer
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hSimpleGen block P source
    | .inr ambient => ambient

end BinarySmallReduced

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

