import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoClosedSourceAssembly
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointCompleteBoundedCatalogueReduced
import SymmetricSubgroupAsymptotics.SixPairActualCompleteRepresentativeSourceBoundedCatalogueReduced

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

namespace PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoClosedSourceAssembly

namespace BoundedCatalogueReduced

def source_of_sixteenPairSource
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (h6 : PublishedPrimitiveDegreeSixClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (publishedTwelve : DegreeTwelveCanonicalCatalogueLocator.PublishedClassification)
    (sixteenPair : DegreeTwoSixteenPairResidualSource) :
    PrimitiveAffineResidualDegreeSource 2 :=
  DegreeTwoGeneralSourceResidualAssembly.source_of_endpoints hZmud lit
    publishedThree (FourPairCanonicalClassification.classification hZmud published8)
    (_root_.SymmetricSubgroupAsymptotics.SixPairActualCompleteRepresentativeSource.BoundedCatalogueReduced.representativeSource
      socle catalogue h6 hZmud lit)
    (PairedEightActualRepresentativeSource.residualSource published8 hZmud lit)
    (degreeTwoTwelvePairResidualSource_of_catalogue
      DegreeTwoTwelvePairFiniteCatalogue.catalogue
      (DegreeTwelveCanonicalCatalogueLocator.locator publishedTwelve)
      (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelveJointComplete.BoundedCatalogueReduced.resolution socle catalogue hZmud lit))
    sixteenPair

end BoundedCatalogueReduced

end PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoClosedSourceAssembly

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

