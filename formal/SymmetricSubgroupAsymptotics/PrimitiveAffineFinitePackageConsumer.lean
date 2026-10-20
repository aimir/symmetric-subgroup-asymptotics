import SymmetricSubgroupAsymptotics.PrimitiveAffineLowDegreeConsumerAssembly

/-! The same affine consumer accepts its already assembled finite package,
so it does not need an unused universal soluble-linear theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
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
    (publishedSmall : PublishedPrimitiveAffineSmallCatalogueData)
    (publishedFinite : PublishedPrimitiveAffineFiniteInput)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (publishedPairs : PublishedDegreeTwoFourPairClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (degreeTwo : PrimitiveAffineResidualDegreeSource 2) :
    PreE7PrimitiveAffineConsumerData := by
  let exceptional := preE7PrimitiveAffineExceptionalCellConsumerData_of_degreeTwoSource
    hZmud lit hgen hClifford hKP hMN hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm hSimpleGen publishedSmall publishedSix publishedPairs published8
    published16 socle degreeTwo
  let components := preE7PrimitiveAffineImprimitiveComponentSourceData publishedSmall
    hcomp hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm exceptional
  refine { primitive := ?_, imprimitive := ?_ }
  · intro w U hw hprimitive P
    exact .inl (publishedFinite.primitiveOwner hcomp hgen hKP U hw hprimitive P)
  · intro w U hw basePoint block P
    exact match components.source w U hw basePoint block P with
    | .inl source => imprimitiveAffineComponentTransfer
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hSimpleGen block P source
    | .inr ambient => ambient

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
