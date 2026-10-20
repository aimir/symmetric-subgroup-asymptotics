import SymmetricSubgroupAsymptotics.SixPairActualCompleteRepresentativeSource
import SymmetricSubgroupAsymptotics.PairedEightActualRepresentativeSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointComplete
import SymmetricSubgroupAsymptotics.DegreeTwelveCanonicalCatalogueLocator
import SymmetricSubgroupAsymptotics.FourPairCanonicalClassification

/-! Valid degree-two frontier assembly from proved original-action sources.
Six and eight pairs use universal geometric sources, and twelve pairs use
the complete actual joint resolution. The four-pair classification and the
project-facing twelve-point locator are constructed internally from bare
point-conjugacy classification.

The sixteen-pair residual source remains an explicit project obligation.
The older finite sixteen-point locator is not assumed: its alternatives do
not establish coverage of the nonzero-odd imprimitive quartet family. This
adapter does not assert unconditional degree-two or T1 closure. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoClosedSourceAssembly

/-- All project-owned source arguments except the honest sixteen-pair
frontier are constructed. Classification inputs contain only literal
isomorphisms or bare point conjugacies. -/
def source_of_sixteenPairSource
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (h6 : PublishedPrimitiveDegreeSixClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (publishedTwelve : DegreeTwelveCanonicalCatalogueLocator.PublishedClassification)
    (sixteenPair : DegreeTwoSixteenPairResidualSource) :
    PrimitiveAffineResidualDegreeSource 2 :=
  DegreeTwoGeneralSourceResidualAssembly.source_of_endpoints hZmud lit
    publishedThree (FourPairCanonicalClassification.classification hZmud published8)
    (SixPairActualCompleteRepresentativeSource.representativeSource
      socle catalogue h6 hZmud lit)
    (PairedEightActualRepresentativeSource.residualSource published8 hZmud lit)
    (degreeTwoTwelvePairResidualSource_of_catalogue
      DegreeTwoTwelvePairFiniteCatalogue.catalogue
      (DegreeTwelveCanonicalCatalogueLocator.locator publishedTwelve)
      (DegreeTwoTwelveJointComplete.resolution socle catalogue hZmud lit))
    sixteenPair

end PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoClosedSourceAssembly
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
