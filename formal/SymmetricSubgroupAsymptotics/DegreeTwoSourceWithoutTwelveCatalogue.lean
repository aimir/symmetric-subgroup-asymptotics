import SymmetricSubgroupAsymptotics.TwelvePairActualComparatorSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoClosedSourceAssemblyDirectConsumers

/-! The actual top comparator removes the301-row twelve-point locator
from the degree-two source factory. All original finite records and the
larger sixteen-pair endpoint are imported unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer

/-- The exact consumer formerly supplied through publishedTwelve, now
constructed for every actual representative without any parameter. -/
def actualTwelvePairRepresentativeSource : DegreeTwoTwelvePairRepresentativeSource :=
  fun p => TwelvePairActualComparatorSource.source p (preE7PairFrame 12 p)

namespace PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoClosedSourceAssembly.ActualTwelve

/-- Keep the existing six-, eight- and sixteen-pair consumers; the entire
twelve-pair branch is supplied by the unconditional actual comparator. -/
def source_of_sixteenPairSource
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (sixteenPair : DegreeTwoSixteenPairResidualSource) :
    PrimitiveAffineResidualDegreeSource 2 :=
  DegreeTwoGeneralSourceResidualAssembly.source_of_endpoints hZmud lit
    publishedThree (FourPairCanonicalClassification.classification hZmud published8)
    (SixPairActualCompleteRepresentativeSource.DirectSix.representativeSource hindex hZmud lit)
    (PairedEightActualRepresentativeSource.residualSource published8 hZmud lit)
    (degreeTwoTwelvePairResidualSource_of_representative actualTwelvePairRepresentativeSource)
    sixteenPair

end PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoClosedSourceAssembly.ActualTwelve
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
