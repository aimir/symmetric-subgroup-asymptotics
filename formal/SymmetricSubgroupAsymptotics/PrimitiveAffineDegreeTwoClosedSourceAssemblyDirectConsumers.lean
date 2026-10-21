import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoClosedSourceAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointCompleteDirectConsumers
import SymmetricSubgroupAsymptotics.SixPairActualCompleteRepresentativeSourceDirectSix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoClosedSourceAssembly.DirectConsumers


def source_of_sixteenPairSource
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (publishedTwelve : DegreeTwelveCanonicalCatalogueLocator.PublishedClassification)
    (sixteenPair : DegreeTwoSixteenPairResidualSource) :
    PrimitiveAffineResidualDegreeSource 2 :=
  DegreeTwoGeneralSourceResidualAssembly.source_of_endpoints hZmud lit
    publishedThree (FourPairCanonicalClassification.classification hZmud published8)
    (SixPairActualCompleteRepresentativeSource.DirectSix.representativeSource
      hindex hZmud lit)
    (PairedEightActualRepresentativeSource.residualSource published8 hZmud lit)
    (degreeTwoTwelvePairResidualSource_of_catalogue
      DegreeTwoTwelvePairFiniteCatalogue.catalogue
      (DegreeTwelveCanonicalCatalogueLocator.locator publishedTwelve)
      (DegreeTwoTwelveJointComplete.DirectConsumers.resolution socle hindex hZmud lit))
    sixteenPair


end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoClosedSourceAssembly.DirectConsumers
