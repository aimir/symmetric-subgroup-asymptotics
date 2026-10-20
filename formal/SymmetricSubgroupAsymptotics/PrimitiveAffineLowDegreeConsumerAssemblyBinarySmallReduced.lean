import SymmetricSubgroupAsymptotics.PrimitiveAffineLowDegreeConsumerAssembly
import SymmetricSubgroupAsymptotics.BinaryAffineSmallCatalogueBridge
import SymmetricSubgroupAsymptotics.PrimitiveAffineExceptionalConsumerPartialAssemblyBinarySmallReduced

/-! Isolated binary-small consumer route. Original datatypes, interfaces,
and finite certificate declarations are imported unchanged. Only the
changed consumer declarations and their private helper closure are copied. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace Non2UnipotentPrefixFiniteMenu

namespace BinarySmallReduced

open PrimitiveAffineImprimitiveBlockTransfer

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
    (published : BinaryAffineSmallCatalogueData)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (publishedPairs : PublishedDegreeTwoFourPairClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (degreeTwo : PrimitiveAffineResidualDegreeSource 2) :
    PreE7PrimitiveAffineExceptionalCellConsumerData :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.preE7PrimitiveAffineExceptionalCellConsumerData_of_lowDegreeSources
    hZmud lit hgen hClifford hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm hSimpleGen published degreeTwo
    (degreeThreeResidualSource hKP publishedSix hZmud lit hClifford
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hgen publishedPairs)
    (degreeFourResidualSource_of_publishedFrames hZmud lit published8
      published16 socle hMN hClifford hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm)

end BinarySmallReduced

end Non2UnipotentPrefixFiniteMenu

end SymmetricSubgroupAsymptotics

