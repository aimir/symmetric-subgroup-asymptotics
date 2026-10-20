import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeConcreteSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourPublishedResidueSource

/-!
# Affine consumer with only the degree-two source left explicit

The concrete degree-three source and the closed degree-four source populate
both remaining low-degree slots of the existing affine assembly. The generic
component dichotomy and the sources at degrees five, eight, nine and sixteen
are supplied by that assembly. The degree-two source and the certificate-valued
four-pair classification remain explicit construction arguments. This does
not assert T1 or discharge any published literature input.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open PrimitiveAffineImprimitiveBlockTransfer

/-- The exceptional-cell consumer after installing the concrete degree-three
and degree-four constructions, retaining degree two as its sole low-degree
construction argument. -/
def preE7PrimitiveAffineExceptionalCellConsumerData_of_degreeTwoSource
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hKP : KovacsPraegerAbelianizationBound)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (published : PublishedPrimitiveAffineSmallCatalogueData)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (publishedPairs : PublishedDegreeTwoFourPairClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (degreeTwo : PrimitiveAffineResidualDegreeSource 2) :
    PreE7PrimitiveAffineExceptionalCellConsumerData :=
  preE7PrimitiveAffineExceptionalCellConsumerData_of_lowDegreeSources
    hZmud lit hgen hClifford hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm hSimpleGen published degreeTwo
    (degreeThreeResidualSource hKP publishedSix hZmud lit hClifford
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hgen publishedPairs)
    (degreeFourResidualSource_of_publishedFrames hZmud lit published8
      published16 socle hMN hClifford hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm)

/-- The full affine consumer, using the existing primitive consumer and
imprimitive component-source dichotomy. The degree-two residual source and
the four-pair classification certificates remain explicit. -/
def preE7PrimitiveAffineConsumerData_of_degreeTwoSource
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
    (published : PublishedPrimitiveAffineFiniteLiterature)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (publishedPairs : PublishedDegreeTwoFourPairClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (degreeTwo : PrimitiveAffineResidualDegreeSource 2) :
    PreE7PrimitiveAffineConsumerData :=
  preE7PrimitiveAffineConsumerData_of_lowDegreeSources
    hZmud lit hgen hClifford hcomp hKP hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm hSimpleGen published degreeTwo
    (degreeThreeResidualSource hKP publishedSix hZmud lit hClifford
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hgen publishedPairs)
    (degreeFourResidualSource_of_publishedFrames hZmud lit published8
      published16 socle hMN hClifford hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
