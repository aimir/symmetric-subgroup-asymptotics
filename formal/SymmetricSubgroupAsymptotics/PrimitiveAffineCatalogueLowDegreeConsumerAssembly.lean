import SymmetricSubgroupAsymptotics.PrimitiveAffineLowDegreeConsumerAssembly
import SymmetricSubgroupAsymptotics.FourPairCanonicalClassification

/-! Low-degree affine composition with the actual four-pair constructor
installed. This milestone is conditional on the degree-two source and the
existing explicit published inputs; it is not completion of T1. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer

def preE7PrimitiveAffineExceptionalCellConsumerData_of_degreeTwoSourceAndCatalogue
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hKP : KovacsPraegerAbelianizationBound)
    (hTracey : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (published : PublishedPrimitiveAffineSmallCatalogueData)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (degreeTwo : PrimitiveAffineResidualDegreeSource 2) :
    PreE7PrimitiveAffineExceptionalCellConsumerData :=
  preE7PrimitiveAffineExceptionalCellConsumerData_of_lowDegreeSources
    hZmud lit hgen hClifford hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm hSimpleGen published degreeTwo
    (degreeThreeResidualSource hKP publishedSix hZmud lit hClifford
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hgen
      (FourPairCanonicalClassification.classification hZmud published8))
    (degreeFourResidualSource_of_publishedFrames hZmud lit published8
      published16 socle hTracey hMN hClifford hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm)

/-- The full affine consumer, using the existing primitive consumer and
imprimitive component-source dichotomy. The degree-two residual source is the only project-owned low-degree
construction input; four-pair correspondence is proved internally. -/
def preE7PrimitiveAffineConsumerData_of_degreeTwoSourceAndCatalogue
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hcomp : PrimitiveCompositionLengthInput)
    (hKP : KovacsPraegerAbelianizationBound)
    (hTracey : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (published : PublishedPrimitiveAffineFiniteLiterature)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (degreeTwo : PrimitiveAffineResidualDegreeSource 2) :
    PreE7PrimitiveAffineConsumerData :=
  preE7PrimitiveAffineConsumerData_of_lowDegreeSources
    hZmud lit hgen hClifford hcomp hKP hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm hSimpleGen published degreeTwo
    (degreeThreeResidualSource hKP publishedSix hZmud lit hClifford
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hgen
      (FourPairCanonicalClassification.classification hZmud published8))
    (degreeFourResidualSource_of_publishedFrames hZmud lit published8
      published16 socle hTracey hMN hClifford hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm)


end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end
