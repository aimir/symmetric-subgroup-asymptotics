import SymmetricSubgroupAsymptotics.DegreeTwoSourceWithoutTwelveCatalogue
import SymmetricSubgroupAsymptotics.SixteenPairActualComparatorSource

/-! The degree-two source factory uses actual complete-moment comparators
at both counts12 and16. The finite pair catalogue datatypes and all older
stronger locator interfaces remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoClosedSourceAssembly.ActualTwelveSixteen

/-- No twelve- or sixteen-point classification is a parameter of the
actual binary-pair source factory. All retained inputs already occur inT1. -/
def source
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hMN : McIverNeumannPermutationGeneratorBound) :
    PrimitiveAffineResidualDegreeSource 2 :=
  DegreeTwoClosedSourceAssembly.ActualTwelve.source_of_sixteenPairSource
    hindex hZmud lit publishedThree published8
    (degreeTwoSixteenPairResidualSource_of_representative
      (actualSixteenPairRepresentativeSource hMN))

end PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoClosedSourceAssembly.ActualTwelveSixteen
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
